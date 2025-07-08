// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace Defs {

  public partial class __default {
    public static bool is__tuple__numeric(Dafny.ISequence<Dafny.Rune> i) {
      return ((((new BigInteger((i).Count)) >= (new BigInteger(2))) && (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_')))) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0123456789")).Contains((i).Select(BigInteger.One)))) && (((new BigInteger((i).Count)) == (new BigInteger(2))) || (((new BigInteger((i).Count)) == (new BigInteger(3))) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0123456789")).Contains((i).Select(new BigInteger(2))))));
    }
    public static bool has__special(Dafny.ISequence<Dafny.Rune> i) {
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return false;
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        return true;
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('#'))) {
        return true;
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        if ((new BigInteger(2)) <= (new BigInteger((i).Count))) {
          if (((i).Select(BigInteger.One)) == (new Dafny.Rune('_'))) {
            Dafny.ISequence<Dafny.Rune> _in0 = (i).Drop(new BigInteger(2));
            i = _in0;
            goto TAIL_CALL_START;
          } else {
            return true;
          }
        } else {
          return true;
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _in1 = (i).Drop(BigInteger.One);
        i = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> idiomatic__rust(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _0___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in0 = (i).Drop(new BigInteger(2));
        i = _in0;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in1 = (i).Drop(BigInteger.One);
        i = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _0___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in0 = (i).Drop(BigInteger.One);
        i = _in0;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in1 = (i).Drop(BigInteger.One);
        i = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static bool is__tuple__builder(Dafny.ISequence<Dafny.Rune> i) {
      return ((((new BigInteger((i).Count)) >= (new BigInteger(9))) && (((i).Take(new BigInteger(8))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("___hMake")))) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0123456789")).Contains((i).Select(new BigInteger(8))))) && (((new BigInteger((i).Count)) == (new BigInteger(9))) || (((new BigInteger((i).Count)) == (new BigInteger(10))) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0123456789")).Contains((i).Select(new BigInteger(9))))));
    }
    public static Dafny.ISequence<Dafny.Rune> better__tuple__builder__name(Dafny.ISequence<Dafny.Rune> i) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), (i).Drop(new BigInteger(8)));
    }
    public static bool is__dafny__generated__id(Dafny.ISequence<Dafny.Rune> i) {
      return (((((new BigInteger((i).Count)).Sign == 1) && (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_')))) && (!(Defs.__default.has__special((i).Drop(BigInteger.One))))) && ((!(i).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_self"))) && (!(i).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_Self"))))) && (!((new BigInteger((i).Count)) >= (new BigInteger(2))) || (((i).Select(BigInteger.One)) != (new Dafny.Rune('T'))));
    }
    public static bool is__idiomatic__rust__id(Dafny.ISequence<Dafny.Rune> i) {
      return ((((new BigInteger((i).Count)).Sign == 1) && (!(Defs.__default.has__special(i)))) && (!(Defs.__default.reserved__rust).Contains(i))) && (!(Defs.__default.reserved__rust__need__prefix).Contains(i));
    }
    public static Dafny.ISequence<Dafny.Rune> escapeName(Dafny.ISequence<Dafny.Rune> n) {
      return Defs.__default.escapeIdent((n));
    }
    public static Dafny.ISequence<Dafny.Rune> escapeIdent(Dafny.ISequence<Dafny.Rune> i) {
      if (Defs.__default.is__tuple__numeric(i)) {
        return i;
      } else if (Defs.__default.is__tuple__builder(i)) {
        return Defs.__default.better__tuple__builder__name(i);
      } else if (((i).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) || ((i).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self")))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), i);
      } else if ((Defs.__default.reserved__rust).Contains(i)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), i);
      } else if (Defs.__default.is__idiomatic__rust__id(i)) {
        return Defs.__default.idiomatic__rust(i);
      } else if (Defs.__default.is__dafny__generated__id(i)) {
        return i;
      } else {
        Dafny.ISequence<Dafny.Rune> _0_r = Defs.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _0_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeVar(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _0_r = (f);
      if ((Defs.__default.reserved__vars).Contains(_0_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _0_r);
      } else {
        return Defs.__default.escapeIdent((f));
      }
    }
    public static Dafny.ISequence<Dafny.Rune> AddAssignedPrefix(Dafny.ISequence<Dafny.Rune> rustName) {
      if (((new BigInteger((rustName).Count)) >= (new BigInteger(2))) && (((rustName).Subsequence(BigInteger.Zero, new BigInteger(2))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Defs.__default.ASSIGNED__PREFIX, (rustName).Drop(new BigInteger(2)));
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Defs.__default.ASSIGNED__PREFIX, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_")), rustName);
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethodAux(Dafny.ISequence<DAST._IType> rs, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _0_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source0 = (rs).Select(BigInteger.Zero);
          {
            if (_source0.is_UserDefined) {
              DAST._IResolvedType _1_resolvedType = _source0.dtor_resolved;
              return Defs.__default.TraitTypeContainingMethod(_1_resolvedType, dafnyName);
            }
          }
          {
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source1 = _0_res;
        {
          if (_source1.is_Some) {
            return _0_res;
          }
        }
        {
          return Defs.__default.TraitTypeContainingMethodAux((rs).Drop(BigInteger.One), dafnyName);
        }
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethod(DAST._IResolvedType r, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DAST._IResolvedType _let_tmp_rhs0 = r;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _0_path = _let_tmp_rhs0.dtor_path;
      Dafny.ISequence<DAST._IType> _1_typeArgs = _let_tmp_rhs0.dtor_typeArgs;
      DAST._IResolvedTypeBase _2_kind = _let_tmp_rhs0.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _3_attributes = _let_tmp_rhs0.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _4_properMethods = _let_tmp_rhs0.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _5_extendedTypes = _let_tmp_rhs0.dtor_extendedTypes;
      if ((_4_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return Defs.__default.TraitTypeContainingMethodAux(_5_extendedTypes, dafnyName);
      }
    }
    public static bool IsRcWrappedDatatypeRec(DAST._IType dafnyType) {
    TAIL_CALL_START: ;
      DAST._IType _source0 = dafnyType;
      {
        if (_source0.is_UserDefined) {
          DAST._IResolvedType resolved0 = _source0.dtor_resolved;
          DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
          if (kind0.is_Datatype) {
            Dafny.ISequence<DAST._IAttribute> _0_attributes = resolved0.dtor_attributes;
            return Defs.__default.IsRcWrapped(_0_attributes);
          }
        }
      }
      {
        if (_source0.is_UserDefined) {
          DAST._IResolvedType resolved1 = _source0.dtor_resolved;
          DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
          if (kind1.is_SynonymType) {
            DAST._IType _1_tpe = kind1.dtor_baseType;
            Dafny.ISequence<DAST._IAttribute> _2_attributes = resolved1.dtor_attributes;
            DAST._IType _in0 = _1_tpe;
            dafnyType = _in0;
            goto TAIL_CALL_START;
          }
        }
      }
      {
        return false;
      }
    }
    public static bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public static Std.Wrappers._IOption<Defs._IExternAttribute> OptExtern(DAST._IAttribute attr, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      if (((attr).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) {
        return Std.Wrappers.Option<Defs._IExternAttribute>.create_Some((((new BigInteger(((attr).dtor_args).Count)).Sign == 0) ? (Defs.ExternAttribute.create_SimpleExtern(Defs.__default.escapeName(dafnyName))) : ((((new BigInteger(((attr).dtor_args).Count)) == (BigInteger.One)) ? (Defs.ExternAttribute.create_SimpleExtern(((attr).dtor_args).Select(BigInteger.Zero))) : ((((new BigInteger(((attr).dtor_args).Count)) == (new BigInteger(2))) ? (Defs.ExternAttribute.create_AdvancedExtern(Defs.__default.SplitRustPathElement(Defs.__default.ReplaceDotByDoubleColon(((attr).dtor_args).Select(BigInteger.Zero)), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), ((attr).dtor_args).Select(BigInteger.One))) : (Defs.ExternAttribute.create_UnsupportedExtern(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{:extern} supports only 0, 1 or 2 attributes, got "), Std.Strings.__default.OfNat(new BigInteger(((attr).dtor_args).Count)))))))))));
      } else {
        return Std.Wrappers.Option<Defs._IExternAttribute>.create_None();
      }
    }
    public static Dafny.ISequence<Dafny.Rune> ReplaceDotByDoubleColon(Dafny.ISequence<Dafny.Rune> s) {
      Dafny.ISequence<Dafny.Rune> _0___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((s).Select(BigInteger.Zero)) == (new Dafny.Rune(' '))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, s);
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, ((((s).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")) : (Dafny.Sequence<Dafny.Rune>.FromElements((s).Select(BigInteger.Zero)))));
        Dafny.ISequence<Dafny.Rune> _in0 = (s).Drop(BigInteger.One);
        s = _in0;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> SplitRustPathElement(Dafny.ISequence<Dafny.Rune> s, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> result, Dafny.ISequence<Dafny.Rune> acc)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        if ((acc).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
          return result;
        } else {
          return Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(result, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(acc));
        }
      } else if (((new BigInteger((s).Count)) >= (new BigInteger(2))) && (((s).Subsequence(BigInteger.Zero, new BigInteger(2))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")))) {
        Dafny.ISequence<Dafny.Rune> _in0 = (s).Drop(new BigInteger(2));
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _in1 = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(result, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(acc));
        Dafny.ISequence<Dafny.Rune> _in2 = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        s = _in0;
        result = _in1;
        acc = _in2;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<Dafny.Rune> _in3 = (s).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _in4 = result;
        Dafny.ISequence<Dafny.Rune> _in5 = Dafny.Sequence<Dafny.Rune>.Concat(acc, Dafny.Sequence<Dafny.Rune>.FromElements((s).Select(BigInteger.Zero)));
        s = _in3;
        result = _in4;
        acc = _in5;
        goto TAIL_CALL_START;
      }
    }
    public static Defs._IExternAttribute ExtractExtern(Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      Defs._IExternAttribute res = Defs.ExternAttribute.Default();
      BigInteger _hi0 = new BigInteger((attributes).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        Std.Wrappers._IOption<Defs._IExternAttribute> _1_attr;
        _1_attr = Defs.__default.OptExtern((attributes).Select(_0_i), dafnyName);
        Std.Wrappers._IOption<Defs._IExternAttribute> _source0 = _1_attr;
        {
          if (_source0.is_Some) {
            Defs._IExternAttribute _2_n = _source0.dtor_value;
            res = _2_n;
            return res;
            goto after_match0;
          }
        }
        {
        }
      after_match0: ;
      }
      res = Defs.ExternAttribute.create_NoExtern();
      return res;
    }
    public static Defs._IExternAttribute ExtractExternMod(DAST._IModule mod) {
      return Defs.__default.ExtractExtern((mod).dtor_attributes, (mod).dtor_name);
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> ContainingPathToRust(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath) {
      return Std.Collections.Seq.__default.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_0_i) => {
        return Defs.__default.escapeName((_0_i));
      })), containingPath);
    }
    public static RAST._IType AddOverflow(RAST._IType tpe, bool overflow)
    {
      if (!(overflow)) {
        return tpe;
      } else {
        return RAST.Type.create_TMetaData(tpe, true, true);
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeRangeToUnwrappedBoundedRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      if ((@base).IsPrimitiveInt()) {
        return Defs.__default.NewtypeRangeToRustType(range);
      } else {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeRangeToRustType(DAST._INewtypeRange range) {
      DAST._INewtypeRange _source0 = range;
      {
        if (_source0.is_NoRange) {
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      {
        if (_source0.is_U8) {
          bool _0_overflow = _source0.dtor_overflow;
          return Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.AddOverflow(RAST.Type.create_U8(), _0_overflow));
        }
      }
      {
        if (_source0.is_U16) {
          bool _1_overflow = _source0.dtor_overflow;
          return Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.AddOverflow(RAST.Type.create_U16(), _1_overflow));
        }
      }
      {
        if (_source0.is_U32) {
          bool _2_overflow = _source0.dtor_overflow;
          return Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.AddOverflow(RAST.Type.create_U32(), _2_overflow));
        }
      }
      {
        if (_source0.is_U64) {
          bool _3_overflow = _source0.dtor_overflow;
          return Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.AddOverflow(RAST.Type.create_U64(), _3_overflow));
        }
      }
      {
        if (_source0.is_U128) {
          bool _4_overflow = _source0.dtor_overflow;
          return Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.AddOverflow(RAST.Type.create_U128(), _4_overflow));
        }
      }
      {
        if (_source0.is_I8) {
          bool _5_overflow = _source0.dtor_overflow;
          return Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.AddOverflow(RAST.Type.create_I8(), _5_overflow));
        }
      }
      {
        if (_source0.is_I16) {
          bool _6_overflow = _source0.dtor_overflow;
          return Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.AddOverflow(RAST.Type.create_I16(), _6_overflow));
        }
      }
      {
        if (_source0.is_I32) {
          bool _7_overflow = _source0.dtor_overflow;
          return Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.AddOverflow(RAST.Type.create_I32(), _7_overflow));
        }
      }
      {
        if (_source0.is_I64) {
          bool _8_overflow = _source0.dtor_overflow;
          return Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.AddOverflow(RAST.Type.create_I64(), _8_overflow));
        }
      }
      {
        if (_source0.is_I128) {
          bool _9_overflow = _source0.dtor_overflow;
          return Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.AddOverflow(RAST.Type.create_I128(), _9_overflow));
        }
      }
      {
        if (_source0.is_NativeArrayIndex) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_USIZE());
        }
      }
      {
        if (_source0.is_Bool) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool());
        }
      }
      {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
    }
    public static bool IsBooleanOperator(DAST._IBinOp op) {
      return ((op).is_And) || ((op).is_Or);
    }
    public static bool IsComplexArithmetic(DAST._IBinOp op) {
      return ((op).is_EuclidianDiv) || ((op).is_EuclidianMod);
    }
    public static Std.Wrappers._IOption<RAST._IType> GetUnwrappedBoundedRustType(DAST._IType tpe) {
      DAST._IType _source0 = tpe;
      {
        if (_source0.is_UserDefined) {
          DAST._IResolvedType resolved0 = _source0.dtor_resolved;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _0_path = resolved0.dtor_path;
          Dafny.ISequence<DAST._IType> _1_typeArgs = resolved0.dtor_typeArgs;
          DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
          if (kind0.is_Newtype) {
            DAST._IType _2_base = kind0.dtor_baseType;
            DAST._INewtypeRange _3_range = kind0.dtor_range;
            bool _4_erase = kind0.dtor_erase;
            return Defs.__default.NewtypeRangeToUnwrappedBoundedRustType(_2_base, _3_range);
          }
        }
      }
      {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
    }
    public static bool NeedsUnwrappingConversion(DAST._IType tpe) {
      DAST._IType _source0 = tpe;
      {
        if (_source0.is_UserDefined) {
          DAST._IResolvedType resolved0 = _source0.dtor_resolved;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _0_path = resolved0.dtor_path;
          Dafny.ISequence<DAST._IType> _1_typeArgs = resolved0.dtor_typeArgs;
          DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
          if (kind0.is_Newtype) {
            DAST._IType _2_base = kind0.dtor_baseType;
            DAST._INewtypeRange _3_range = kind0.dtor_range;
            bool _4_erase = kind0.dtor_erase;
            return (Defs.__default.NewtypeRangeToUnwrappedBoundedRustType(_2_base, _3_range)).is_None;
          }
        }
      }
      {
        return false;
      }
    }
    public static bool IsNewtype(DAST._IType tpe) {
      return ((tpe).is_UserDefined) && ((((tpe).dtor_resolved).dtor_kind).is_Newtype);
    }
    public static bool IsNewtypeCopy(DAST._INewtypeRange range) {
      return ((Defs.__default.NewtypeRangeToRustType(range)).is_Some) && (((range).HasArithmeticOperations()) || ((range).is_Bool));
    }
    public static bool OwnershipGuarantee(Defs._IOwnership expectedOwnership, Defs._IOwnership resultingOwnership)
    {
      return (!(!object.Equals(expectedOwnership, Defs.Ownership.create_OwnershipAutoBorrowed())) || (object.Equals(resultingOwnership, expectedOwnership))) && (!object.Equals(resultingOwnership, Defs.Ownership.create_OwnershipAutoBorrowed()));
    }
    public static bool BecomesLeftCallsRight(DAST._IBinOp op) {
      DAST._IBinOp _source0 = op;
      {
        bool disjunctiveMatch0 = false;
        if (_source0.is_SetMerge) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_SetSubtraction) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_SetIntersection) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_SetDisjoint) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MapMerge) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MapSubtraction) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MultisetMerge) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MultisetSubtraction) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MultisetIntersection) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_MultisetDisjoint) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_Concat) {
          disjunctiveMatch0 = true;
        }
        if (disjunctiveMatch0) {
          return true;
        }
      }
      {
        return false;
      }
    }
    public static bool BecomesRightCallsLeft(DAST._IBinOp op) {
      DAST._IBinOp _source0 = op;
      {
        if (_source0.is_In) {
          return true;
        }
      }
      {
        return false;
      }
    }
    public static RAST._IExpr Panic(Dafny.ISequence<Dafny.Rune> optText) {
      if ((optText).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
        return (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply0();
      } else {
        return (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(optText, false, false));
      }
    }
    public static RAST._IExpr UnreachablePanicIfVerified(Defs._IPointerType pointerType, Dafny.ISequence<Dafny.Rune> optText)
    {
      if ((pointerType).is_Raw) {
        return RAST.__default.Unsafe(RAST.Expr.create_Block(((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hint"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unreachable_unchecked"))).Apply0()));
      } else {
        return Defs.__default.Panic(optText);
      }
    }
    public static RAST._IModDecl DefaultDatatypeImpl(Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, RAST._IType datatypeType, RAST._IExpr datatypeName, Dafny.ISequence<RAST._IAssignIdentifier> structAssignments)
    {
      Dafny.ISequence<RAST._ITypeParamDecl> _0_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      return RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_0_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, datatypeType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(datatypeType), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(datatypeName, structAssignments)))))));
    }
    public static RAST._IModDecl AsRefDatatypeImpl(Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, RAST._IType datatypeType)
    {
      return RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDecls, ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).AsType()).Apply1(datatypeType), datatypeType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfBorrowed), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))));
    }
    public static RAST._IModDecl DebugImpl(Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, RAST._IType datatypeType, Dafny.ISequence<RAST._IType> rTypeParams)
    {
      return RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug"))).AsType(), datatypeType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType()))), Std.Wrappers.Option<RAST._IType>.create_Some((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Result"))).AsType()), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true)))))))));
    }
    public static RAST._IModDecl PrintImpl(Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, RAST._IType datatypeType, Dafny.ISequence<RAST._IType> rTypeParams, RAST._IExpr printImplBody)
    {
      return RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDecls, RAST.__default.DafnyPrint, datatypeType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType())), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Std.Wrappers.Option<RAST._IExpr>.create_Some(printImplBody))))));
    }
    public static Dafny.ISequence<RAST._IModDecl> EqImpl(Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDeclsWithEq, RAST._IType datatypeType, Dafny.ISequence<RAST._IType> rTypeParams, RAST._IExpr eqImplBody)
    {
      return Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDeclsWithEq, RAST.__default.PartialEq, datatypeType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfBorrowed)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(eqImplBody)))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDeclsWithEq, RAST.__default.Eq, datatypeType, Dafny.Sequence<RAST._IImplMember>.FromElements())));
    }
    public static RAST._IModDecl CoerceImpl(Func<RAST._IType, RAST._IType> rc, Func<RAST._IExpr, RAST._IExpr> rcNew, Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, Dafny.ISequence<Dafny.Rune> datatypeName, RAST._IType datatypeType, Dafny.ISequence<RAST._ITypeParamDecl> rCoerceTypeParams, Dafny.ISequence<RAST._IFormal> coerceArguments, Dafny.ISequence<RAST._IType> coerceTypes, RAST._IExpr coerceImplBody)
    {
      return RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(rTypeParamsDecls, datatypeType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Given type parameter conversions, returns a lambda to convert this structure"), RAST.__default.NoAttr, RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), rCoerceTypeParams, coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(Dafny.Helpers.Id<Func<RAST._IType, RAST._IType>>(rc)(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(datatypeType), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(datatypeName), coerceTypes))))), Std.Wrappers.Option<RAST._IExpr>.create_Some(Dafny.Helpers.Id<Func<RAST._IExpr, RAST._IExpr>>(rcNew)(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.__default.SelfOwned)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(datatypeName), coerceTypes)), coerceImplBody))))))));
    }
    public static RAST._IModDecl SingletonsImpl(Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, RAST._IType datatypeType, RAST._IType instantiationType, Dafny.ISequence<RAST._IExpr> singletonConstructors)
    {
      return RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(rTypeParamsDecls, datatypeType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Enumerates all possible values of "), (datatypeType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<RAST._IAttribute>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_AllSingletonConstructors"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SequenceIter"))).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(instantiationType))), Std.Wrappers.Option<RAST._IExpr>.create_Some((((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).AsExpr()).Apply(singletonConstructors)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply0()))))));
    }
    public static RAST._IModDecl HashImpl(Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDeclsWithHash, RAST._IType datatypeOrNewtypeType, RAST._IExpr hashImplBody)
    {
      return RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDeclsWithHash, RAST.__default.Hash, datatypeOrNewtypeType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Defs.__default.hash__type__parameters, Defs.__default.hash__parameters, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(hashImplBody))))));
    }
    public static RAST._IImplMember hasher__trait(bool supportsEquality, Defs._IPointerType pointerType)
    {
      return RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64()), Std.Wrappers.Option<RAST._IExpr>.create_Some(((supportsEquality) ? ((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hasher"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DefaultHasher"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply0()))).Then((((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut"), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hasher")), DAST.Format.UnaryOpFormat.create_NoFormat()))).Then(((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hasher"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("finish"))).Apply0()))) : (Defs.__default.UnreachablePanicIfVerified(pointerType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The type does not support equality")))))));
    }
    public static RAST._IImplMember eq__trait(RAST._IType fullTraitPath, RAST._IExpr fullTraitExpr, bool supportsEquality, Defs._IPointerType pointerType)
    {
      return RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_eq"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.Type.create_Borrowed(RAST.__default.Box(RAST.Type.create_DynType(fullTraitPath))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(((supportsEquality) ? ((((((((fullTraitExpr).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_as_any"))).Apply1(((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply0())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("downcast_ref"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.SelfOwned))).Apply0()).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map_or"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralBool(false), RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_")))), Std.Wrappers.Option<RAST._IType>.create_None(), RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x")), DAST.Format.BinaryOpFormat.create_NoFormat()))))) : (Defs.__default.UnreachablePanicIfVerified(pointerType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The type does not support equality")))))));
    }
    public static RAST._IImplMember clone__trait(RAST._IType fullTraitPath) {
      return RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_clone"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Box(RAST.Type.create_DynType(fullTraitPath))), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.BoxNew(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply0()))));
    }
    public static RAST._IModDecl UnaryOpsImpl(Dafny.Rune op, Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, RAST._IType newtypeType, Dafny.ISequence<Dafny.Rune> newtypeConstructor)
    {
      _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs0 = ((System.Func<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>>)(() => {
        Dafny.Rune _source0 = op;
        {
          return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Not"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("not"));
        }
      }))();
      Dafny.ISequence<Dafny.Rune> _0_traitName = _let_tmp_rhs0.dtor__0;
      Dafny.ISequence<Dafny.Rune> _1_methodName = _let_tmp_rhs0.dtor__1;
      return RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ops"))).MSel(_0_traitName)).AsType(), newtypeType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_TypeDeclMember(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Output"), newtypeType), RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(_1_methodName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfOwned), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Std.Wrappers.Option<RAST._IExpr>.create_Some((RAST.Expr.create_Identifier(newtypeConstructor)).Apply1(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.FromElements(op), (RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.UnaryOpFormat.create_NoFormat()))))))));
    }
    public static RAST._IModDecl OpsImpl(Dafny.Rune op, Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, RAST._IType newtypeType, Dafny.ISequence<Dafny.Rune> newtypeConstructor)
    {
      _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs0 = ((System.Func<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>>)(() => {
        Dafny.Rune _source0 = op;
        {
          if ((_source0) == (new Dafny.Rune('+'))) {
            return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Add"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add"));
          }
        }
        {
          if ((_source0) == (new Dafny.Rune('-'))) {
            return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sub"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("sub"));
          }
        }
        {
          if ((_source0) == (new Dafny.Rune('/'))) {
            return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Div"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("div"));
          }
        }
        {
          return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Mul"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mul"));
        }
      }))();
      Dafny.ISequence<Dafny.Rune> _0_traitName = _let_tmp_rhs0.dtor__0;
      Dafny.ISequence<Dafny.Rune> _1_methodName = _let_tmp_rhs0.dtor__1;
      return RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ops"))).MSel(_0_traitName)).AsType(), newtypeType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_TypeDeclMember(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Output"), newtypeType), RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(_1_methodName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfOwned, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfOwned)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Std.Wrappers.Option<RAST._IExpr>.create_Some((RAST.Expr.create_Identifier(newtypeConstructor)).Apply1(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.FromElements(op), (RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat()))))))));
    }
    public static RAST._IModDecl PartialOrdImpl(Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, RAST._IType newtypeType, Dafny.ISequence<Dafny.Rune> newtypeConstructor)
    {
      return RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cmp"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PartialOrd"))).AsType(), newtypeType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("partial_cmp"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"), RAST.__default.SelfBorrowed)), Std.Wrappers.Option<RAST._IType>.create_Some(((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("option"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Option"))).AsType()).Apply1((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cmp"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ordering"))).AsType())), Std.Wrappers.Option<RAST._IExpr>.create_Some((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cmp"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PartialOrd"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("partial_cmp"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.Borrow((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))), RAST.__default.Borrow((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("other"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))))))))));
    }
    public static Std.Wrappers._IOption<RAST._IModDecl> DowncastTraitDeclFor(Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, RAST._IType fullType)
    {
      Std.Wrappers._IOption<RAST._IType> _0_valueOrError0 = (fullType).ToDowncast();
      if ((_0_valueOrError0).IsFailure()) {
        return (_0_valueOrError0).PropagateFailure<RAST._IModDecl>();
      } else {
        RAST._IType _1_downcast__type = (_0_valueOrError0).Extract();
        return Std.Wrappers.Option<RAST._IModDecl>.create_Some(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(RAST.__default.NoDoc, RAST.__default.NoAttr, rTypeParamsDecls, _1_downcast__type, Dafny.Sequence<RAST._IType>.FromElements(), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_None())), RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_as"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(fullType), Std.Wrappers.Option<RAST._IExpr>.create_None()))))));
      }
    }
    public static Std.Wrappers._IOption<RAST._IModDecl> DowncastImplFor(Func<RAST._IExpr, RAST._IExpr> rcNew, Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, RAST._IType datatypeType)
    {
      Std.Wrappers._IOption<RAST._IType> _0_valueOrError0 = (datatypeType).ToDowncast();
      if ((_0_valueOrError0).IsFailure()) {
        return (_0_valueOrError0).PropagateFailure<RAST._IModDecl>();
      } else {
        RAST._IType _1_downcast__type = (_0_valueOrError0).Extract();
        bool _2_isRc = (datatypeType).IsRc();
        RAST._IType _3_datatypeTypeRaw = ((_2_isRc) ? ((datatypeType).RcUnderlying()) : (datatypeType));
        RAST._IExpr _4_isBody = (((((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("downcast_ref"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_3_datatypeTypeRaw))).Apply0()).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is_some"))).Apply0();
        RAST._IExpr _5_asBody = (((((((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("downcast_ref"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_3_datatypeTypeRaw))).Apply0()).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply0()).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply0();
        RAST._IExpr _6_asBody = ((_2_isRc) ? (Dafny.Helpers.Id<Func<RAST._IExpr, RAST._IExpr>>(rcNew)(_5_asBody)) : (_5_asBody));
        return Std.Wrappers.Option<RAST._IModDecl>.create_Some(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDecls, _1_downcast__type, RAST.Type.create_DynType(RAST.__default.AnyTrait), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(_4_isBody))), RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_as"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(datatypeType), Std.Wrappers.Option<RAST._IExpr>.create_Some(_6_asBody)))))));
      }
    }
    public static Std.Wrappers._IOption<RAST._IModDecl> DowncastNotImplFor(Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, RAST._IType traitType, RAST._IType datatypeType)
    {
      Std.Wrappers._IOption<RAST._IType> _0_valueOrError0 = (traitType).ToDowncast();
      if ((_0_valueOrError0).IsFailure()) {
        return (_0_valueOrError0).PropagateFailure<RAST._IModDecl>();
      } else {
        RAST._IType _1_downcast__type = (_0_valueOrError0).Extract();
        bool _2_isRc = (datatypeType).IsRc();
        RAST._IType _3_datatypeTypeRaw = ((_2_isRc) ? ((datatypeType).RcUnderlying()) : (datatypeType));
        RAST._IExpr _4_isBody = RAST.Expr.create_LiteralBool(false);
        RAST._IExpr _5_asBody = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply0();
        return Std.Wrappers.Option<RAST._IModDecl>.create_Some(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDecls, _1_downcast__type, _3_datatypeTypeRaw, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(Dafny.Sequence<Dafny.Rune>.Concat((_3_datatypeTypeRaw)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" does not implement that trait")), RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(_4_isBody))), RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_as"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(traitType), Std.Wrappers.Option<RAST._IExpr>.create_Some(_5_asBody)))))));
      }
    }
    public static Std.Wrappers._IOption<RAST._IModDecl> DowncastImplTraitFor(Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, RAST._IType traitType, bool implementsTrait, RAST._IType datatypeType)
    {
      Std.Wrappers._IOption<RAST._IType> _0_valueOrError0 = (traitType).ToDowncast();
      if ((_0_valueOrError0).IsFailure()) {
        return (_0_valueOrError0).PropagateFailure<RAST._IModDecl>();
      } else {
        RAST._IType _1_downcast__type = (_0_valueOrError0).Extract();
        bool _2_isRc = (datatypeType).IsRc();
        RAST._IType _3_forType = ((_2_isRc) ? ((datatypeType).RcUnderlying()) : (datatypeType));
        RAST._IType _4_resultType = traitType;
        RAST._IExpr _5_isBody = RAST.Expr.create_LiteralBool(implementsTrait);
        RAST._IExpr _6_asBody = RAST.__default.BoxNew((RAST.__default.self).Clone());
        return Std.Wrappers.Option<RAST._IModDecl>.create_Some(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDecls, _1_downcast__type, _3_forType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(_5_isBody))), RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_as"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(_4_resultType), Std.Wrappers.Option<RAST._IExpr>.create_Some(_6_asBody)))))));
      }
    }
    public static RAST._IModDecl UpcastDynTraitFor(Dafny.ISequence<RAST._ITypeParamDecl> rTypeParamsDecls, RAST._IType forBoxedTraitType, RAST._IType superTraitType, RAST._IExpr superTraitExpr)
    {
      RAST._IType _0_superBoxedTraitType = RAST.__default.Box(RAST.Type.create_DynType(superTraitType));
      RAST._IExpr _1_body = ((superTraitExpr).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_clone"))).Apply1(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply0());
      return RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastBox"))).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(superTraitType))), forBoxedTraitType, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(_0_superBoxedTraitType), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1_body))))));
    }
    public static Defs._IAssignmentStatus DetectAssignmentStatus(Dafny.ISequence<DAST._IStatement> stmts__remainder, Dafny.ISequence<Dafny.Rune> dafny__name)
    {
      Defs._IAssignmentStatus _hresult = Defs.AssignmentStatus.Default();
      BigInteger _hi0 = new BigInteger((stmts__remainder).Count);
      for (BigInteger _0_i = BigInteger.Zero; _0_i < _hi0; _0_i++) {
        DAST._IStatement _1_stmt;
        _1_stmt = (stmts__remainder).Select(_0_i);
        DAST._IStatement _source0 = _1_stmt;
        {
          if (_source0.is_Assign) {
            DAST._IAssignLhs lhs0 = _source0.dtor_lhs;
            if (lhs0.is_Ident) {
              Dafny.ISequence<Dafny.Rune> _2_assign__name = lhs0.dtor_ident;
              if (object.Equals(_2_assign__name, dafny__name)) {
                _hresult = Defs.AssignmentStatus.create_SurelyAssigned();
                return _hresult;
              }
              goto after_match0;
            }
          }
        }
        {
          if (_source0.is_If) {
            DAST._IExpression _3_cond = _source0.dtor_cond;
            Dafny.ISequence<DAST._IStatement> _4_thn = _source0.dtor_thn;
            Dafny.ISequence<DAST._IStatement> _5_els = _source0.dtor_els;
            Defs._IAssignmentStatus _6_rec;
            _6_rec = Defs.__default.DetectAssignmentStatus(_4_thn, dafny__name);
            if (object.Equals(_6_rec, Defs.AssignmentStatus.create_Unknown())) {
              _hresult = Defs.AssignmentStatus.create_Unknown();
              return _hresult;
            }
            Defs._IAssignmentStatus _7_rec2;
            _7_rec2 = Defs.__default.DetectAssignmentStatus(_5_els, dafny__name);
            if (object.Equals(_7_rec2, Defs.AssignmentStatus.create_Unknown())) {
              _hresult = Defs.AssignmentStatus.create_Unknown();
              return _hresult;
            }
            if (!object.Equals(_6_rec, _7_rec2)) {
              _hresult = Defs.AssignmentStatus.create_Unknown();
              return _hresult;
            }
            if ((_6_rec).is_SurelyAssigned) {
              _hresult = Defs.AssignmentStatus.create_SurelyAssigned();
              return _hresult;
            }
            goto after_match0;
          }
        }
        {
          if (_source0.is_Call) {
            DAST._IExpression _8_on = _source0.dtor_on;
            DAST._ICallName _9_callName = _source0.dtor_callName;
            Dafny.ISequence<DAST._IType> _10_typeArgs = _source0.dtor_typeArgs;
            Dafny.ISequence<DAST._IExpression> _11_args = _source0.dtor_args;
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _12_outs = _source0.dtor_outs;
            if (((_12_outs).is_Some) && (((_12_outs).dtor_value).Contains(dafny__name))) {
              _hresult = Defs.AssignmentStatus.create_SurelyAssigned();
              return _hresult;
            }
            goto after_match0;
          }
        }
        {
          if (_source0.is_Labeled) {
            Dafny.ISequence<DAST._IStatement> _13_stmts = _source0.dtor_body;
            Defs._IAssignmentStatus _14_rec;
            _14_rec = Defs.__default.DetectAssignmentStatus(_13_stmts, dafny__name);
            if (!((_14_rec).is_NotAssigned)) {
              _hresult = _14_rec;
              return _hresult;
            }
            goto after_match0;
          }
        }
        {
          if (_source0.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _15_name = _source0.dtor_name;
            if (object.Equals(_15_name, dafny__name)) {
              _hresult = Defs.AssignmentStatus.create_NotAssigned();
              return _hresult;
            }
            goto after_match0;
          }
        }
        {
          bool disjunctiveMatch0 = false;
          if (_source0.is_Return) {
            disjunctiveMatch0 = true;
          }
          if (_source0.is_EarlyReturn) {
            disjunctiveMatch0 = true;
          }
          if (_source0.is_JumpTailCallStart) {
            disjunctiveMatch0 = true;
          }
          if (disjunctiveMatch0) {
            _hresult = Defs.AssignmentStatus.create_NotAssigned();
            return _hresult;
            goto after_match0;
          }
        }
        {
          if (_source0.is_Print) {
            goto after_match0;
          }
        }
        {
          _hresult = Defs.AssignmentStatus.create_Unknown();
          return _hresult;
        }
      after_match0: ;
      }
      _hresult = Defs.AssignmentStatus.create_NotAssigned();
      return _hresult;
      return _hresult;
    }
    public static Dafny.ISequence<Dafny.Rune> prefixWith2(Dafny.ISequence<Dafny.Rune> s) {
      if (((new BigInteger((s).Count)) >= (new BigInteger(2))) && (((s).Take(new BigInteger(2))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_2_"), (s).Drop(new BigInteger(2)));
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_2_"), s);
      }
    }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust__1 { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("async"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("await"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("const"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("else"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("enum"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("loop"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mod"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mut"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ref"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"));
    } }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust__2 { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("static"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("struct"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("trait"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("union"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("use"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("where"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Keywords"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abstract"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("become"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("box"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("do"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("final"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("macro"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("override"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("priv"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("try"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("typeof"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsized"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("virtual"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("yield"));
    } }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Defs.__default.reserved__rust__1, Defs.__default.reserved__rust__2);
    } }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust__need__prefix { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u8"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u16"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u32"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u64"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u128"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i8"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i16"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i32"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i64"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i128"));
    } }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__vars { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"));
    } }
    public static Dafny.ISequence<Dafny.Rune> ASSIGNED__PREFIX { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_set");
    } }
    public static Dafny.ISequence<RAST._ITypeParamDecl> hash__type__parameters { get {
      return Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))).AsType())));
    } }
    public static Dafny.ISequence<RAST._IFormal> hash__parameters { get {
      return Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H")))));
    } }
    public static Dafny.ISequence<RAST._IFormal> fmt__print__parameters { get {
      return Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType())), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool()));
    } }
    public static RAST._IType fmt__print__result { get {
      return (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Result"))).AsType();
    } }
    public static RAST._IImplMember print__trait { get {
      return RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Defs.__default.fmt__print__parameters, Std.Wrappers.Option<RAST._IType>.create_Some(Defs.__default.fmt__print__result), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.__default.self).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter")), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq")))))));
    } }
    public static Dafny.ISequence<Dafny.Rune> IND { get {
      return RAST.__default.IND;
    } }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> builtin__trait__preferred__methods { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("le"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("eq"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("lt"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ge"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("gt"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"));
    } }
    public static DAST._IAttribute AttributeOwned { get {
      return DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("owned"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
    } }
    public static Dafny.ISequence<Dafny.Rune> TailRecursionPrefix { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_r");
    } }
    public static Dafny.ISequence<Dafny.Rune> DAFNY__EXTERN__MODULE { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_dafny_externs");
    } }
    public static Dafny.IMap<DAST._IBinOp,Dafny.ISequence<Dafny.Rune>> OpTable { get {
      return Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Mod(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_And(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Or(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Div(false), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Lt(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_LtChar(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Plus(false), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Minus(false), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Times(false), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseAnd(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseOr(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseXor(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftRight(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftLeft(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<")));
    } }
    public static RAST._IExpr hash__function { get {
      return ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hash"))).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"));
    } }
    public static RAST._IImplMember as__any__trait { get {
      return RAST.ImplMember.create_FnDecl(RAST.__default.NoDoc, RAST.__default.NoAttr, RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_as_any"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(RAST.Type.create_DynType(RAST.__default.AnyTrait))), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self)));
    } }
  }

  public interface _IOwnership {
    bool is_OwnershipOwned { get; }
    bool is_OwnershipBorrowed { get; }
    bool is_OwnershipBorrowedMut { get; }
    bool is_OwnershipAutoBorrowed { get; }
    _IOwnership DowncastClone();
  }
  public abstract class Ownership : _IOwnership {
    public Ownership() {
    }
    private static readonly Defs._IOwnership theDefault = create_OwnershipOwned();
    public static Defs._IOwnership Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Defs._IOwnership> _TYPE = new Dafny.TypeDescriptor<Defs._IOwnership>(Defs.Ownership.Default());
    public static Dafny.TypeDescriptor<Defs._IOwnership> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IOwnership create_OwnershipOwned() {
      return new Ownership_OwnershipOwned();
    }
    public static _IOwnership create_OwnershipBorrowed() {
      return new Ownership_OwnershipBorrowed();
    }
    public static _IOwnership create_OwnershipBorrowedMut() {
      return new Ownership_OwnershipBorrowedMut();
    }
    public static _IOwnership create_OwnershipAutoBorrowed() {
      return new Ownership_OwnershipAutoBorrowed();
    }
    public bool is_OwnershipOwned { get { return this is Ownership_OwnershipOwned; } }
    public bool is_OwnershipBorrowed { get { return this is Ownership_OwnershipBorrowed; } }
    public bool is_OwnershipBorrowedMut { get { return this is Ownership_OwnershipBorrowedMut; } }
    public bool is_OwnershipAutoBorrowed { get { return this is Ownership_OwnershipAutoBorrowed; } }
    public static System.Collections.Generic.IEnumerable<_IOwnership> AllSingletonConstructors {
      get {
        yield return Ownership.create_OwnershipOwned();
        yield return Ownership.create_OwnershipBorrowed();
        yield return Ownership.create_OwnershipBorrowedMut();
        yield return Ownership.create_OwnershipAutoBorrowed();
      }
    }
    public abstract _IOwnership DowncastClone();
  }
  public class Ownership_OwnershipOwned : Ownership {
    public Ownership_OwnershipOwned() : base() {
    }
    public override _IOwnership DowncastClone() {
      if (this is _IOwnership dt) { return dt; }
      return new Ownership_OwnershipOwned();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.Ownership_OwnershipOwned;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.Ownership.OwnershipOwned";
      return s;
    }
  }
  public class Ownership_OwnershipBorrowed : Ownership {
    public Ownership_OwnershipBorrowed() : base() {
    }
    public override _IOwnership DowncastClone() {
      if (this is _IOwnership dt) { return dt; }
      return new Ownership_OwnershipBorrowed();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.Ownership_OwnershipBorrowed;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.Ownership.OwnershipBorrowed";
      return s;
    }
  }
  public class Ownership_OwnershipBorrowedMut : Ownership {
    public Ownership_OwnershipBorrowedMut() : base() {
    }
    public override _IOwnership DowncastClone() {
      if (this is _IOwnership dt) { return dt; }
      return new Ownership_OwnershipBorrowedMut();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.Ownership_OwnershipBorrowedMut;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.Ownership.OwnershipBorrowedMut";
      return s;
    }
  }
  public class Ownership_OwnershipAutoBorrowed : Ownership {
    public Ownership_OwnershipAutoBorrowed() : base() {
    }
    public override _IOwnership DowncastClone() {
      if (this is _IOwnership dt) { return dt; }
      return new Ownership_OwnershipAutoBorrowed();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.Ownership_OwnershipAutoBorrowed;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.Ownership.OwnershipAutoBorrowed";
      return s;
    }
  }

  public interface _IEnvironment {
    bool is_Environment { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_names { get; }
    Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> dtor_types { get; }
    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> dtor_assignmentStatusKnown { get; }
    _IEnvironment DowncastClone();
    Defs._IEnvironment ToOwned();
    bool CanReadWithoutClone(Dafny.ISequence<Dafny.Rune> name);
    bool HasCloneSemantics(Dafny.ISequence<Dafny.Rune> name);
    Std.Wrappers._IOption<RAST._IType> GetType(Dafny.ISequence<Dafny.Rune> name);
    bool IsBorrowed(Dafny.ISequence<Dafny.Rune> name);
    bool IsBorrowedMut(Dafny.ISequence<Dafny.Rune> name);
    bool IsBoxed(Dafny.ISequence<Dafny.Rune> name);
    bool NeedsAsRefForBorrow(Dafny.ISequence<Dafny.Rune> name);
    bool IsMaybePlacebo(Dafny.ISequence<Dafny.Rune> name);
    Defs._IEnvironment AddAssigned(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe);
    Defs._IEnvironment Merge(Defs._IEnvironment other);
    Defs._IEnvironment Join(Defs._IEnvironment thenBranch, Defs._IEnvironment elseBranch);
    Defs._IEnvironment RemoveAssigned(Dafny.ISequence<Dafny.Rune> name);
    Defs._IEnvironment AddAssignmentStatus(Dafny.ISequence<Dafny.Rune> name, Defs._IAssignmentStatus assignmentStatus);
    bool IsAssignmentStatusKnown(Dafny.ISequence<Dafny.Rune> name);
  }
  public class Environment : _IEnvironment {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _names;
    public readonly Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _types;
    public readonly Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _assignmentStatusKnown;
    public Environment(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> types, Dafny.ISet<Dafny.ISequence<Dafny.Rune>> assignmentStatusKnown) {
      this._names = names;
      this._types = types;
      this._assignmentStatusKnown = assignmentStatusKnown;
    }
    public _IEnvironment DowncastClone() {
      if (this is _IEnvironment dt) { return dt; }
      return new Environment(_names, _types, _assignmentStatusKnown);
    }
    public override bool Equals(object other) {
      var oth = other as Defs.Environment;
      return oth != null && object.Equals(this._names, oth._names) && object.Equals(this._types, oth._types) && object.Equals(this._assignmentStatusKnown, oth._assignmentStatusKnown);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._names));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._types));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._assignmentStatusKnown));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.Environment.Environment";
      s += "(";
      s += Dafny.Helpers.ToString(this._names);
      s += ", ";
      s += Dafny.Helpers.ToString(this._types);
      s += ", ";
      s += Dafny.Helpers.ToString(this._assignmentStatusKnown);
      s += ")";
      return s;
    }
    private static readonly Defs._IEnvironment theDefault = create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty, Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Empty, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty);
    public static Defs._IEnvironment Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Defs._IEnvironment> _TYPE = new Dafny.TypeDescriptor<Defs._IEnvironment>(Defs.Environment.Default());
    public static Dafny.TypeDescriptor<Defs._IEnvironment> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnvironment create(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> types, Dafny.ISet<Dafny.ISequence<Dafny.Rune>> assignmentStatusKnown) {
      return new Environment(names, types, assignmentStatusKnown);
    }
    public static _IEnvironment create_Environment(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> types, Dafny.ISet<Dafny.ISequence<Dafny.Rune>> assignmentStatusKnown) {
      return create(names, types, assignmentStatusKnown);
    }
    public bool is_Environment { get { return true; } }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_names {
      get {
        return this._names;
      }
    }
    public Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> dtor_types {
      get {
        return this._types;
      }
    }
    public Dafny.ISet<Dafny.ISequence<Dafny.Rune>> dtor_assignmentStatusKnown {
      get {
        return this._assignmentStatusKnown;
      }
    }
    public Defs._IEnvironment ToOwned() {
      Defs._IEnvironment _0_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll0 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_0 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _2_k = (Dafny.ISequence<Dafny.Rune>)_compr_0;
          if (((this).dtor_types).Contains(_2_k)) {
            _coll0.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_2_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_2_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll0);
      }))();
      return Defs.Environment.create((_0_dt__update__tmp_h0).dtor_names, _1_dt__update_htypes_h0, (_0_dt__update__tmp_h0).dtor_assignmentStatusKnown);
    }
    public static Defs._IEnvironment Empty() {
      return Defs.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements());
    }
    public bool CanReadWithoutClone(Dafny.ISequence<Dafny.Rune> name) {
      return (((this).dtor_types).Contains(name)) && ((Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,name)).CanReadWithoutClone());
    }
    public bool HasCloneSemantics(Dafny.ISequence<Dafny.Rune> name) {
      return !((this).CanReadWithoutClone(name));
    }
    public Std.Wrappers._IOption<RAST._IType> GetType(Dafny.ISequence<Dafny.Rune> name) {
      if (((this).dtor_types).Contains(name)) {
        return Std.Wrappers.Option<RAST._IType>.create_Some(Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,name));
      } else {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
    }
    public bool IsBorrowed(Dafny.ISequence<Dafny.Rune> name) {
      return (((this).dtor_types).Contains(name)) && ((Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,name)).is_Borrowed);
    }
    public bool IsBorrowedMut(Dafny.ISequence<Dafny.Rune> name) {
      return (((this).dtor_types).Contains(name)) && ((Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,name)).is_BorrowedMut);
    }
    public bool IsBoxed(Dafny.ISequence<Dafny.Rune> name) {
      return (((this).dtor_types).Contains(name)) && ((Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,name)).IsBox());
    }
    public bool NeedsAsRefForBorrow(Dafny.ISequence<Dafny.Rune> name) {
      return (((this).dtor_types).Contains(name)) && ((Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,name)).NeedsAsRefForBorrow());
    }
    public bool IsMaybePlacebo(Dafny.ISequence<Dafny.Rune> name) {
      return (((this).dtor_types).Contains(name)) && (((Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,name)).ExtractMaybePlacebo()).is_Some);
    }
    public Defs._IEnvironment AddAssigned(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe)
    {
      return Defs.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((this).dtor_names, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(name)), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update((this).dtor_types, name, tpe), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference((this).dtor_assignmentStatusKnown, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
    }
    public Defs._IEnvironment Merge(Defs._IEnvironment other) {
      return Defs.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((this).dtor_names, (other).dtor_names), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge((this).dtor_types, (other).dtor_types), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union((this).dtor_assignmentStatusKnown, (other).dtor_assignmentStatusKnown));
    }
    public Defs._IEnvironment Join(Defs._IEnvironment thenBranch, Defs._IEnvironment elseBranch)
    {
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _0_removed = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(((this).dtor_types).Keys, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(((thenBranch).dtor_types).Keys, ((elseBranch).dtor_types).Keys));
      return Defs.Environment.create(Std.Collections.Seq.__default.Filter<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.Id<Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>, Func<Dafny.ISequence<Dafny.Rune>, bool>>>((_1_removed) => ((System.Func<Dafny.ISequence<Dafny.Rune>, bool>)((_2_name) => {
  return !(_1_removed).Contains(_2_name);
})))(_0_removed), (this).dtor_names), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, _0_removed), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference((this).dtor_assignmentStatusKnown, _0_removed));
    }
    public Defs._IEnvironment RemoveAssigned(Dafny.ISequence<Dafny.Rune> name) {
      BigInteger _0_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return Defs.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _0_indexInEnv), ((this).dtor_names).Drop((_0_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference((this).dtor_assignmentStatusKnown, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
    }
    public Defs._IEnvironment AddAssignmentStatus(Dafny.ISequence<Dafny.Rune> name, Defs._IAssignmentStatus assignmentStatus)
    {
      return Defs.Environment.create((this).dtor_names, (this).dtor_types, (((assignmentStatus).is_Unknown) ? (Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference((this).dtor_assignmentStatusKnown, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name))) : (Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union((this).dtor_assignmentStatusKnown, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)))));
    }
    public bool IsAssignmentStatusKnown(Dafny.ISequence<Dafny.Rune> name) {
      return ((this).dtor_assignmentStatusKnown).Contains(name);
    }
  }

  public interface _IPointerType {
    bool is_Raw { get; }
    bool is_RcMut { get; }
    _IPointerType DowncastClone();
  }
  public abstract class PointerType : _IPointerType {
    public PointerType() {
    }
    private static readonly Defs._IPointerType theDefault = create_Raw();
    public static Defs._IPointerType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Defs._IPointerType> _TYPE = new Dafny.TypeDescriptor<Defs._IPointerType>(Defs.PointerType.Default());
    public static Dafny.TypeDescriptor<Defs._IPointerType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPointerType create_Raw() {
      return new PointerType_Raw();
    }
    public static _IPointerType create_RcMut() {
      return new PointerType_RcMut();
    }
    public bool is_Raw { get { return this is PointerType_Raw; } }
    public bool is_RcMut { get { return this is PointerType_RcMut; } }
    public static System.Collections.Generic.IEnumerable<_IPointerType> AllSingletonConstructors {
      get {
        yield return PointerType.create_Raw();
        yield return PointerType.create_RcMut();
      }
    }
    public abstract _IPointerType DowncastClone();
  }
  public class PointerType_Raw : PointerType {
    public PointerType_Raw() : base() {
    }
    public override _IPointerType DowncastClone() {
      if (this is _IPointerType dt) { return dt; }
      return new PointerType_Raw();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.PointerType_Raw;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.PointerType.Raw";
      return s;
    }
  }
  public class PointerType_RcMut : PointerType {
    public PointerType_RcMut() : base() {
    }
    public override _IPointerType DowncastClone() {
      if (this is _IPointerType dt) { return dt; }
      return new PointerType_RcMut();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.PointerType_RcMut;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.PointerType.RcMut";
      return s;
    }
  }

  public interface _ICharType {
    bool is_UTF16 { get; }
    bool is_UTF32 { get; }
    _ICharType DowncastClone();
  }
  public abstract class CharType : _ICharType {
    public CharType() {
    }
    private static readonly Defs._ICharType theDefault = create_UTF16();
    public static Defs._ICharType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Defs._ICharType> _TYPE = new Dafny.TypeDescriptor<Defs._ICharType>(Defs.CharType.Default());
    public static Dafny.TypeDescriptor<Defs._ICharType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICharType create_UTF16() {
      return new CharType_UTF16();
    }
    public static _ICharType create_UTF32() {
      return new CharType_UTF32();
    }
    public bool is_UTF16 { get { return this is CharType_UTF16; } }
    public bool is_UTF32 { get { return this is CharType_UTF32; } }
    public static System.Collections.Generic.IEnumerable<_ICharType> AllSingletonConstructors {
      get {
        yield return CharType.create_UTF16();
        yield return CharType.create_UTF32();
      }
    }
    public abstract _ICharType DowncastClone();
  }
  public class CharType_UTF16 : CharType {
    public CharType_UTF16() : base() {
    }
    public override _ICharType DowncastClone() {
      if (this is _ICharType dt) { return dt; }
      return new CharType_UTF16();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.CharType_UTF16;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.CharType.UTF16";
      return s;
    }
  }
  public class CharType_UTF32 : CharType {
    public CharType_UTF32() : base() {
    }
    public override _ICharType DowncastClone() {
      if (this is _ICharType dt) { return dt; }
      return new CharType_UTF32();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.CharType_UTF32;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.CharType.UTF32";
      return s;
    }
  }

  public interface _IRootType {
    bool is_RootCrate { get; }
    bool is_RootPath { get; }
    Dafny.ISequence<Dafny.Rune> dtor_moduleName { get; }
    _IRootType DowncastClone();
  }
  public abstract class RootType : _IRootType {
    public RootType() {
    }
    private static readonly Defs._IRootType theDefault = create_RootCrate();
    public static Defs._IRootType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Defs._IRootType> _TYPE = new Dafny.TypeDescriptor<Defs._IRootType>(Defs.RootType.Default());
    public static Dafny.TypeDescriptor<Defs._IRootType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRootType create_RootCrate() {
      return new RootType_RootCrate();
    }
    public static _IRootType create_RootPath(Dafny.ISequence<Dafny.Rune> moduleName) {
      return new RootType_RootPath(moduleName);
    }
    public bool is_RootCrate { get { return this is RootType_RootCrate; } }
    public bool is_RootPath { get { return this is RootType_RootPath; } }
    public Dafny.ISequence<Dafny.Rune> dtor_moduleName {
      get {
        var d = this;
        return ((RootType_RootPath)d)._moduleName;
      }
    }
    public abstract _IRootType DowncastClone();
  }
  public class RootType_RootCrate : RootType {
    public RootType_RootCrate() : base() {
    }
    public override _IRootType DowncastClone() {
      if (this is _IRootType dt) { return dt; }
      return new RootType_RootCrate();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.RootType_RootCrate;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.RootType.RootCrate";
      return s;
    }
  }
  public class RootType_RootPath : RootType {
    public readonly Dafny.ISequence<Dafny.Rune> _moduleName;
    public RootType_RootPath(Dafny.ISequence<Dafny.Rune> moduleName) : base() {
      this._moduleName = moduleName;
    }
    public override _IRootType DowncastClone() {
      if (this is _IRootType dt) { return dt; }
      return new RootType_RootPath(_moduleName);
    }
    public override bool Equals(object other) {
      var oth = other as Defs.RootType_RootPath;
      return oth != null && object.Equals(this._moduleName, oth._moduleName);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._moduleName));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.RootType.RootPath";
      s += "(";
      s += this._moduleName.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }

  public interface _ISyncType {
    bool is_NoSync { get; }
    bool is_Sync { get; }
    _ISyncType DowncastClone();
  }
  public abstract class SyncType : _ISyncType {
    public SyncType() {
    }
    private static readonly Defs._ISyncType theDefault = create_NoSync();
    public static Defs._ISyncType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Defs._ISyncType> _TYPE = new Dafny.TypeDescriptor<Defs._ISyncType>(Defs.SyncType.Default());
    public static Dafny.TypeDescriptor<Defs._ISyncType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISyncType create_NoSync() {
      return new SyncType_NoSync();
    }
    public static _ISyncType create_Sync() {
      return new SyncType_Sync();
    }
    public bool is_NoSync { get { return this is SyncType_NoSync; } }
    public bool is_Sync { get { return this is SyncType_Sync; } }
    public static System.Collections.Generic.IEnumerable<_ISyncType> AllSingletonConstructors {
      get {
        yield return SyncType.create_NoSync();
        yield return SyncType.create_Sync();
      }
    }
    public abstract _ISyncType DowncastClone();
  }
  public class SyncType_NoSync : SyncType {
    public SyncType_NoSync() : base() {
    }
    public override _ISyncType DowncastClone() {
      if (this is _ISyncType dt) { return dt; }
      return new SyncType_NoSync();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.SyncType_NoSync;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.SyncType.NoSync";
      return s;
    }
  }
  public class SyncType_Sync : SyncType {
    public SyncType_Sync() : base() {
    }
    public override _ISyncType DowncastClone() {
      if (this is _ISyncType dt) { return dt; }
      return new SyncType_Sync();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.SyncType_Sync;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.SyncType.Sync";
      return s;
    }
  }

  public interface _IGenTypeContext {
    bool is_GenTypeContext { get; }
    bool dtor_forTraitParents { get; }
  }
  public class GenTypeContext : _IGenTypeContext {
    public readonly bool _forTraitParents;
    public GenTypeContext(bool forTraitParents) {
      this._forTraitParents = forTraitParents;
    }
    public static bool DowncastClone(bool _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as Defs.GenTypeContext;
      return oth != null && this._forTraitParents == oth._forTraitParents;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._forTraitParents));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.GenTypeContext.GenTypeContext";
      s += "(";
      s += Dafny.Helpers.ToString(this._forTraitParents);
      s += ")";
      return s;
    }
    private static readonly bool theDefault = false;
    public static bool Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<bool> _TYPE = new Dafny.TypeDescriptor<bool>(false);
    public static Dafny.TypeDescriptor<bool> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenTypeContext create(bool forTraitParents) {
      return new GenTypeContext(forTraitParents);
    }
    public static _IGenTypeContext create_GenTypeContext(bool forTraitParents) {
      return create(forTraitParents);
    }
    public bool is_GenTypeContext { get { return true; } }
    public bool dtor_forTraitParents {
      get {
        return this._forTraitParents;
      }
    }
    public static bool ForTraitParents() {
      return true;
    }
    public static bool @default() {
      return false;
    }
  }

  public interface _ISelfInfo {
    bool is_NoSelf { get; }
    bool is_ThisTyped { get; }
    Dafny.ISequence<Dafny.Rune> dtor_rSelfName { get; }
    DAST._IType dtor_dafnyType { get; }
    _ISelfInfo DowncastClone();
    bool IsSelf();
    bool IsGeneralTrait();
    bool IsClassOrObjectTrait();
    bool IsRcWrappedDatatype();
  }
  public abstract class SelfInfo : _ISelfInfo {
    public SelfInfo() {
    }
    private static readonly Defs._ISelfInfo theDefault = create_NoSelf();
    public static Defs._ISelfInfo Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Defs._ISelfInfo> _TYPE = new Dafny.TypeDescriptor<Defs._ISelfInfo>(Defs.SelfInfo.Default());
    public static Dafny.TypeDescriptor<Defs._ISelfInfo> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISelfInfo create_NoSelf() {
      return new SelfInfo_NoSelf();
    }
    public static _ISelfInfo create_ThisTyped(Dafny.ISequence<Dafny.Rune> rSelfName, DAST._IType dafnyType) {
      return new SelfInfo_ThisTyped(rSelfName, dafnyType);
    }
    public bool is_NoSelf { get { return this is SelfInfo_NoSelf; } }
    public bool is_ThisTyped { get { return this is SelfInfo_ThisTyped; } }
    public Dafny.ISequence<Dafny.Rune> dtor_rSelfName {
      get {
        var d = this;
        return ((SelfInfo_ThisTyped)d)._rSelfName;
      }
    }
    public DAST._IType dtor_dafnyType {
      get {
        var d = this;
        return ((SelfInfo_ThisTyped)d)._dafnyType;
      }
    }
    public abstract _ISelfInfo DowncastClone();
    public bool IsSelf() {
      return ((this).is_ThisTyped) && (((this).dtor_rSelfName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")));
    }
    public bool IsGeneralTrait() {
      return ((this).is_ThisTyped) && (((this).dtor_dafnyType).IsGeneralTrait());
    }
    public bool IsClassOrObjectTrait() {
      return ((this).is_ThisTyped) && (((this).dtor_dafnyType).IsClassOrObjectTrait());
    }
    public bool IsRcWrappedDatatype() {
      return ((this).is_ThisTyped) && (Defs.__default.IsRcWrappedDatatypeRec((this).dtor_dafnyType));
    }
  }
  public class SelfInfo_NoSelf : SelfInfo {
    public SelfInfo_NoSelf() : base() {
    }
    public override _ISelfInfo DowncastClone() {
      if (this is _ISelfInfo dt) { return dt; }
      return new SelfInfo_NoSelf();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.SelfInfo_NoSelf;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.SelfInfo.NoSelf";
      return s;
    }
  }
  public class SelfInfo_ThisTyped : SelfInfo {
    public readonly Dafny.ISequence<Dafny.Rune> _rSelfName;
    public readonly DAST._IType _dafnyType;
    public SelfInfo_ThisTyped(Dafny.ISequence<Dafny.Rune> rSelfName, DAST._IType dafnyType) : base() {
      this._rSelfName = rSelfName;
      this._dafnyType = dafnyType;
    }
    public override _ISelfInfo DowncastClone() {
      if (this is _ISelfInfo dt) { return dt; }
      return new SelfInfo_ThisTyped(_rSelfName, _dafnyType);
    }
    public override bool Equals(object other) {
      var oth = other as Defs.SelfInfo_ThisTyped;
      return oth != null && object.Equals(this._rSelfName, oth._rSelfName) && object.Equals(this._dafnyType, oth._dafnyType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rSelfName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dafnyType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.SelfInfo.ThisTyped";
      s += "(";
      s += this._rSelfName.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._dafnyType);
      s += ")";
      return s;
    }
  }

  public interface _IExternAttribute {
    bool is_NoExtern { get; }
    bool is_SimpleExtern { get; }
    bool is_AdvancedExtern { get; }
    bool is_UnsupportedExtern { get; }
    Dafny.ISequence<Dafny.Rune> dtor_overrideName { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_enclosingModule { get; }
    Dafny.ISequence<Dafny.Rune> dtor_reason { get; }
    _IExternAttribute DowncastClone();
  }
  public abstract class ExternAttribute : _IExternAttribute {
    public ExternAttribute() {
    }
    private static readonly Defs._IExternAttribute theDefault = create_NoExtern();
    public static Defs._IExternAttribute Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Defs._IExternAttribute> _TYPE = new Dafny.TypeDescriptor<Defs._IExternAttribute>(Defs.ExternAttribute.Default());
    public static Dafny.TypeDescriptor<Defs._IExternAttribute> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IExternAttribute create_NoExtern() {
      return new ExternAttribute_NoExtern();
    }
    public static _IExternAttribute create_SimpleExtern(Dafny.ISequence<Dafny.Rune> overrideName) {
      return new ExternAttribute_SimpleExtern(overrideName);
    }
    public static _IExternAttribute create_AdvancedExtern(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> enclosingModule, Dafny.ISequence<Dafny.Rune> overrideName) {
      return new ExternAttribute_AdvancedExtern(enclosingModule, overrideName);
    }
    public static _IExternAttribute create_UnsupportedExtern(Dafny.ISequence<Dafny.Rune> reason) {
      return new ExternAttribute_UnsupportedExtern(reason);
    }
    public bool is_NoExtern { get { return this is ExternAttribute_NoExtern; } }
    public bool is_SimpleExtern { get { return this is ExternAttribute_SimpleExtern; } }
    public bool is_AdvancedExtern { get { return this is ExternAttribute_AdvancedExtern; } }
    public bool is_UnsupportedExtern { get { return this is ExternAttribute_UnsupportedExtern; } }
    public Dafny.ISequence<Dafny.Rune> dtor_overrideName {
      get {
        var d = this;
        if (d is ExternAttribute_SimpleExtern) { return ((ExternAttribute_SimpleExtern)d)._overrideName; }
        return ((ExternAttribute_AdvancedExtern)d)._overrideName;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_enclosingModule {
      get {
        var d = this;
        return ((ExternAttribute_AdvancedExtern)d)._enclosingModule;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_reason {
      get {
        var d = this;
        return ((ExternAttribute_UnsupportedExtern)d)._reason;
      }
    }
    public abstract _IExternAttribute DowncastClone();
  }
  public class ExternAttribute_NoExtern : ExternAttribute {
    public ExternAttribute_NoExtern() : base() {
    }
    public override _IExternAttribute DowncastClone() {
      if (this is _IExternAttribute dt) { return dt; }
      return new ExternAttribute_NoExtern();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.ExternAttribute_NoExtern;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.ExternAttribute.NoExtern";
      return s;
    }
  }
  public class ExternAttribute_SimpleExtern : ExternAttribute {
    public readonly Dafny.ISequence<Dafny.Rune> _overrideName;
    public ExternAttribute_SimpleExtern(Dafny.ISequence<Dafny.Rune> overrideName) : base() {
      this._overrideName = overrideName;
    }
    public override _IExternAttribute DowncastClone() {
      if (this is _IExternAttribute dt) { return dt; }
      return new ExternAttribute_SimpleExtern(_overrideName);
    }
    public override bool Equals(object other) {
      var oth = other as Defs.ExternAttribute_SimpleExtern;
      return oth != null && object.Equals(this._overrideName, oth._overrideName);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overrideName));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.ExternAttribute.SimpleExtern";
      s += "(";
      s += this._overrideName.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class ExternAttribute_AdvancedExtern : ExternAttribute {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _enclosingModule;
    public readonly Dafny.ISequence<Dafny.Rune> _overrideName;
    public ExternAttribute_AdvancedExtern(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> enclosingModule, Dafny.ISequence<Dafny.Rune> overrideName) : base() {
      this._enclosingModule = enclosingModule;
      this._overrideName = overrideName;
    }
    public override _IExternAttribute DowncastClone() {
      if (this is _IExternAttribute dt) { return dt; }
      return new ExternAttribute_AdvancedExtern(_enclosingModule, _overrideName);
    }
    public override bool Equals(object other) {
      var oth = other as Defs.ExternAttribute_AdvancedExtern;
      return oth != null && object.Equals(this._enclosingModule, oth._enclosingModule) && object.Equals(this._overrideName, oth._overrideName);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._enclosingModule));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overrideName));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.ExternAttribute.AdvancedExtern";
      s += "(";
      s += Dafny.Helpers.ToString(this._enclosingModule);
      s += ", ";
      s += this._overrideName.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class ExternAttribute_UnsupportedExtern : ExternAttribute {
    public readonly Dafny.ISequence<Dafny.Rune> _reason;
    public ExternAttribute_UnsupportedExtern(Dafny.ISequence<Dafny.Rune> reason) : base() {
      this._reason = reason;
    }
    public override _IExternAttribute DowncastClone() {
      if (this is _IExternAttribute dt) { return dt; }
      return new ExternAttribute_UnsupportedExtern(_reason);
    }
    public override bool Equals(object other) {
      var oth = other as Defs.ExternAttribute_UnsupportedExtern;
      return oth != null && object.Equals(this._reason, oth._reason);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._reason));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.ExternAttribute.UnsupportedExtern";
      s += "(";
      s += this._reason.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }

  public interface _IAssignmentStatus {
    bool is_NotAssigned { get; }
    bool is_SurelyAssigned { get; }
    bool is_Unknown { get; }
    _IAssignmentStatus DowncastClone();
    Defs._IAssignmentStatus Join(Defs._IAssignmentStatus other);
    Defs._IAssignmentStatus Then(Defs._IAssignmentStatus other);
  }
  public abstract class AssignmentStatus : _IAssignmentStatus {
    public AssignmentStatus() {
    }
    private static readonly Defs._IAssignmentStatus theDefault = create_NotAssigned();
    public static Defs._IAssignmentStatus Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Defs._IAssignmentStatus> _TYPE = new Dafny.TypeDescriptor<Defs._IAssignmentStatus>(Defs.AssignmentStatus.Default());
    public static Dafny.TypeDescriptor<Defs._IAssignmentStatus> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAssignmentStatus create_NotAssigned() {
      return new AssignmentStatus_NotAssigned();
    }
    public static _IAssignmentStatus create_SurelyAssigned() {
      return new AssignmentStatus_SurelyAssigned();
    }
    public static _IAssignmentStatus create_Unknown() {
      return new AssignmentStatus_Unknown();
    }
    public bool is_NotAssigned { get { return this is AssignmentStatus_NotAssigned; } }
    public bool is_SurelyAssigned { get { return this is AssignmentStatus_SurelyAssigned; } }
    public bool is_Unknown { get { return this is AssignmentStatus_Unknown; } }
    public static System.Collections.Generic.IEnumerable<_IAssignmentStatus> AllSingletonConstructors {
      get {
        yield return AssignmentStatus.create_NotAssigned();
        yield return AssignmentStatus.create_SurelyAssigned();
        yield return AssignmentStatus.create_Unknown();
      }
    }
    public abstract _IAssignmentStatus DowncastClone();
    public Defs._IAssignmentStatus Join(Defs._IAssignmentStatus other) {
      if (((this).is_SurelyAssigned) && ((other).is_SurelyAssigned)) {
        return Defs.AssignmentStatus.create_SurelyAssigned();
      } else if (((this).is_NotAssigned) && ((other).is_NotAssigned)) {
        return Defs.AssignmentStatus.create_NotAssigned();
      } else {
        return Defs.AssignmentStatus.create_Unknown();
      }
    }
    public Defs._IAssignmentStatus Then(Defs._IAssignmentStatus other) {
      if ((this).is_SurelyAssigned) {
        return Defs.AssignmentStatus.create_SurelyAssigned();
      } else if ((this).is_NotAssigned) {
        return other;
      } else {
        return Defs.AssignmentStatus.create_Unknown();
      }
    }
  }
  public class AssignmentStatus_NotAssigned : AssignmentStatus {
    public AssignmentStatus_NotAssigned() : base() {
    }
    public override _IAssignmentStatus DowncastClone() {
      if (this is _IAssignmentStatus dt) { return dt; }
      return new AssignmentStatus_NotAssigned();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.AssignmentStatus_NotAssigned;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.AssignmentStatus.NotAssigned";
      return s;
    }
  }
  public class AssignmentStatus_SurelyAssigned : AssignmentStatus {
    public AssignmentStatus_SurelyAssigned() : base() {
    }
    public override _IAssignmentStatus DowncastClone() {
      if (this is _IAssignmentStatus dt) { return dt; }
      return new AssignmentStatus_SurelyAssigned();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.AssignmentStatus_SurelyAssigned;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.AssignmentStatus.SurelyAssigned";
      return s;
    }
  }
  public class AssignmentStatus_Unknown : AssignmentStatus {
    public AssignmentStatus_Unknown() : base() {
    }
    public override _IAssignmentStatus DowncastClone() {
      if (this is _IAssignmentStatus dt) { return dt; }
      return new AssignmentStatus_Unknown();
    }
    public override bool Equals(object other) {
      var oth = other as Defs.AssignmentStatus_Unknown;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompilerDefinitions.AssignmentStatus.Unknown";
      return s;
    }
  }
} // end of namespace Defs