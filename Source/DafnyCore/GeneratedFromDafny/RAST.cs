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

namespace RAST {

  public partial class __default {
    public static __A FoldLeft<__A, __T>(Func<__A, __T, __A> f, __A init, Dafny.ISequence<__T> xs)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return init;
      } else {
        Func<__A, __T, __A> _in0 = f;
        __A _in1 = Dafny.Helpers.Id<Func<__A, __T, __A>>(f)(init, (xs).Select(BigInteger.Zero));
        Dafny.ISequence<__T> _in2 = (xs).Drop(BigInteger.One);
        f = _in0;
        init = _in1;
        xs = _in2;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> GatherSimpleQuotes(Dafny.ISequence<Dafny.Rune> docstring, Dafny.ISequence<Dafny.Rune> acc)
    {
    TAIL_CALL_START: ;
      if (((new BigInteger((docstring).Count)).Sign == 0) || (((docstring).Select(BigInteger.Zero)) != (new Dafny.Rune('`')))) {
        return acc;
      } else {
        Dafny.ISequence<Dafny.Rune> _in0 = (docstring).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in1 = Dafny.Sequence<Dafny.Rune>.Concat(acc, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("`"));
        docstring = _in0;
        acc = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> ConvertDocstring(Dafny.ISequence<Dafny.Rune> dafnyDocstring, Dafny.ISequence<Dafny.Rune> ind, bool newlineStarted, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> codeMarker)
    {
      Dafny.ISequence<Dafny.Rune> _0___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((dafnyDocstring).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, dafnyDocstring);
      } else if (((dafnyDocstring).Select(BigInteger.Zero)) == (new Dafny.Rune('\n'))) {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.DocStringPrefix));
        Dafny.ISequence<Dafny.Rune> _in0 = (dafnyDocstring).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in1 = ind;
        bool _in2 = true;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _in3 = codeMarker;
        dafnyDocstring = _in0;
        ind = _in1;
        newlineStarted = _in2;
        codeMarker = _in3;
        goto TAIL_CALL_START;
      } else if (((dafnyDocstring).Select(BigInteger.Zero)) == (new Dafny.Rune(' '))) {
        if (((((codeMarker).is_None) && (newlineStarted)) && ((new BigInteger((dafnyDocstring).Count)) > (new BigInteger(4)))) && (((dafnyDocstring).Take(new BigInteger(4))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("    ")))) {
          _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|   "));
          Dafny.ISequence<Dafny.Rune> _in4 = (dafnyDocstring).Drop(new BigInteger(4));
          Dafny.ISequence<Dafny.Rune> _in5 = ind;
          bool _in6 = false;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _in7 = codeMarker;
          dafnyDocstring = _in4;
          ind = _in5;
          newlineStarted = _in6;
          codeMarker = _in7;
          goto TAIL_CALL_START;
        } else {
          _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
          Dafny.ISequence<Dafny.Rune> _in8 = (dafnyDocstring).Drop(BigInteger.One);
          Dafny.ISequence<Dafny.Rune> _in9 = ind;
          bool _in10 = newlineStarted;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _in11 = codeMarker;
          dafnyDocstring = _in8;
          ind = _in9;
          newlineStarted = _in10;
          codeMarker = _in11;
          goto TAIL_CALL_START;
        }
      } else if (newlineStarted) {
        if ((((codeMarker).is_Some) && ((new BigInteger((dafnyDocstring).Count)) >= ((new BigInteger(((codeMarker).dtor_value).Count)) + (BigInteger.One)))) && (((dafnyDocstring).Take((new BigInteger(((codeMarker).dtor_value).Count)) + (BigInteger.One))).Equals(Dafny.Sequence<Dafny.Rune>.Concat((codeMarker).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"))))) {
          _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, (codeMarker).dtor_value);
          Dafny.ISequence<Dafny.Rune> _in12 = (dafnyDocstring).Drop(new BigInteger(((codeMarker).dtor_value).Count));
          Dafny.ISequence<Dafny.Rune> _in13 = ind;
          bool _in14 = false;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _in15 = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
          dafnyDocstring = _in12;
          ind = _in13;
          newlineStarted = _in14;
          codeMarker = _in15;
          goto TAIL_CALL_START;
        } else if (((codeMarker).is_None) && ((new BigInteger((dafnyDocstring).Count)) >= (new BigInteger(3)))) {
          Dafny.ISequence<Dafny.Rune> _1_prefix = (dafnyDocstring).Take(new BigInteger(3));
          if ((_1_prefix).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("```"))) {
            Dafny.ISequence<Dafny.Rune> _2_prefix = RAST.__default.GatherSimpleQuotes(dafnyDocstring, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            Dafny.ISequence<Dafny.Rune> _3_remaining = (dafnyDocstring).Drop(new BigInteger((_2_prefix).Count));
            if ((((new BigInteger((_3_remaining).Count)).Sign == 0) || (((_3_remaining).Select(BigInteger.Zero)) == (new Dafny.Rune(' ')))) || (((_3_remaining).Select(BigInteger.Zero)) == (new Dafny.Rune('\n')))) {
              _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.Concat(_2_prefix, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny")));
              Dafny.ISequence<Dafny.Rune> _in16 = (dafnyDocstring).Drop(new BigInteger((_2_prefix).Count));
              Dafny.ISequence<Dafny.Rune> _in17 = ind;
              bool _in18 = false;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _in19 = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2_prefix);
              dafnyDocstring = _in16;
              ind = _in17;
              newlineStarted = _in18;
              codeMarker = _in19;
              goto TAIL_CALL_START;
            } else if ((((new BigInteger((_3_remaining).Count)) >= (new BigInteger(3))) && (((_3_remaining).Take(new BigInteger(2))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rs")))) && ((((_3_remaining).Select(new BigInteger(2))) == (new Dafny.Rune(' '))) || (((_3_remaining).Select(new BigInteger(2))) == (new Dafny.Rune('\n'))))) {
              _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, _2_prefix);
              Dafny.ISequence<Dafny.Rune> _in20 = (dafnyDocstring).Drop((new BigInteger((_2_prefix).Count)) + (new BigInteger(2)));
              Dafny.ISequence<Dafny.Rune> _in21 = ind;
              bool _in22 = false;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _in23 = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2_prefix);
              dafnyDocstring = _in20;
              ind = _in21;
              newlineStarted = _in22;
              codeMarker = _in23;
              goto TAIL_CALL_START;
            } else {
              _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, _2_prefix);
              Dafny.ISequence<Dafny.Rune> _in24 = (dafnyDocstring).Drop(new BigInteger((_2_prefix).Count));
              Dafny.ISequence<Dafny.Rune> _in25 = ind;
              bool _in26 = false;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _in27 = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2_prefix);
              dafnyDocstring = _in24;
              ind = _in25;
              newlineStarted = _in26;
              codeMarker = _in27;
              goto TAIL_CALL_START;
            }
          } else {
            _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, (dafnyDocstring).Take(BigInteger.One));
            Dafny.ISequence<Dafny.Rune> _in28 = (dafnyDocstring).Drop(BigInteger.One);
            Dafny.ISequence<Dafny.Rune> _in29 = ind;
            bool _in30 = false;
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _in31 = codeMarker;
            dafnyDocstring = _in28;
            ind = _in29;
            newlineStarted = _in30;
            codeMarker = _in31;
            goto TAIL_CALL_START;
          }
        } else if ((((codeMarker).is_Some) && ((new BigInteger(((codeMarker).dtor_value).Count)) <= (new BigInteger((dafnyDocstring).Count)))) && (((dafnyDocstring).Take(new BigInteger(((codeMarker).dtor_value).Count))).Equals((codeMarker).dtor_value))) {
          _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, (codeMarker).dtor_value);
          Dafny.ISequence<Dafny.Rune> _in32 = (dafnyDocstring).Drop(new BigInteger(((codeMarker).dtor_value).Count));
          Dafny.ISequence<Dafny.Rune> _in33 = ind;
          bool _in34 = false;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _in35 = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
          dafnyDocstring = _in32;
          ind = _in33;
          newlineStarted = _in34;
          codeMarker = _in35;
          goto TAIL_CALL_START;
        } else {
          _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, (dafnyDocstring).Take(BigInteger.One));
          Dafny.ISequence<Dafny.Rune> _in36 = (dafnyDocstring).Drop(BigInteger.One);
          Dafny.ISequence<Dafny.Rune> _in37 = ind;
          bool _in38 = false;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _in39 = codeMarker;
          dafnyDocstring = _in36;
          ind = _in37;
          newlineStarted = _in38;
          codeMarker = _in39;
          goto TAIL_CALL_START;
        }
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, (dafnyDocstring).Take(BigInteger.One));
        Dafny.ISequence<Dafny.Rune> _in40 = (dafnyDocstring).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in41 = ind;
        bool _in42 = false;
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _in43 = codeMarker;
        dafnyDocstring = _in40;
        ind = _in41;
        newlineStarted = _in42;
        codeMarker = _in43;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> ToDocstringPrefix(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<Dafny.Rune> ind)
    {
      if ((docString).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.DocStringPrefix, RAST.__default.ConvertDocstring(docString, ind, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> SeqToString<__T>(Dafny.ISequence<__T> s, Func<__T, Dafny.ISequence<Dafny.Rune>> f, Dafny.ISequence<Dafny.Rune> separator)
    {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Helpers.Id<Func<__T, Dafny.ISequence<Dafny.Rune>>>(f)((s).Select(BigInteger.Zero)), (((new BigInteger((s).Count)) > (BigInteger.One)) ? (Dafny.Sequence<Dafny.Rune>.Concat(separator, RAST.__default.SeqToString<__T>((s).Drop(BigInteger.One), f, separator))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))));
      }
    }
    public static RAST._IType ObjectType(RAST._IType underlying) {
      return ((RAST.__default.ObjectPath).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(underlying));
    }
    public static RAST._IType PtrType(RAST._IType underlying) {
      return ((RAST.__default.PtrPath).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(underlying));
    }
    public static RAST._IType RefCell(RAST._IType underlying) {
      return RAST.Type.create_TypeApp(RAST.__default.RefcellType, Dafny.Sequence<RAST._IType>.FromElements(underlying));
    }
    public static RAST._IType Vec(RAST._IType underlying) {
      return RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Vec"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(underlying));
    }
    public static RAST._IExpr NewVec(Dafny.ISequence<RAST._IExpr> elements) {
      return (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("vec!"))).Apply(elements);
    }
    public static RAST._IExpr Borrow(RAST._IExpr underlying) {
      return RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), underlying, DAST.Format.UnaryOpFormat.create_NoFormat());
    }
    public static RAST._IExpr BorrowMut(RAST._IExpr underlying) {
      return RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut"), underlying, DAST.Format.UnaryOpFormat.create_NoFormat());
    }
    public static RAST._IType RawType(Dafny.ISequence<Dafny.Rune> content) {
      return RAST.Type.create_TIdentifier(content);
    }
    public static RAST._IType Box(RAST._IType content) {
      return RAST.Type.create_TypeApp((RAST.__default.BoxPath).AsType(), Dafny.Sequence<RAST._IType>.FromElements(content));
    }
    public static RAST._IExpr BoxNew(RAST._IExpr content) {
      return (((RAST.__default.BoxPath).AsExpr()).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(content));
    }
    public static RAST._IType SystemTupleType(Dafny.ISequence<RAST._IType> elements) {
      return ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"))).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Tuple"), Std.Strings.__default.OfNat(new BigInteger((elements).Count))))).AsType()).Apply(elements);
    }
    public static RAST._IExpr SystemTuple(Dafny.ISequence<RAST._IExpr> elements) {
      Dafny.ISequence<Dafny.Rune> _0_size = Std.Strings.__default.OfNat(new BigInteger((elements).Count));
      return RAST.Expr.create_StructBuild(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"))).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Tuple"), _0_size))).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), _0_size))).AsExpr(), ((System.Func<Dafny.ISequence<RAST._IAssignIdentifier>>) (() => {
  BigInteger dim14 = new BigInteger((elements).Count);
  var arr14 = new RAST._IAssignIdentifier[Dafny.Helpers.ToIntChecked(dim14, "array size exceeds memory limit")];
  for (int i14 = 0; i14 < dim14; i14++) {
    var _1_i = (BigInteger) i14;
    arr14[(int)(_1_i)] = RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), Std.Strings.__default.OfNat(_1_i)), (elements).Select(_1_i));
  }
  return Dafny.Sequence<RAST._IAssignIdentifier>.FromArray(arr14);
}))());
    }
    public static RAST._IType MaybeUninitType(RAST._IType underlying) {
      return (RAST.__default.MaybeUninitPathType).Apply(Dafny.Sequence<RAST._IType>.FromElements(underlying));
    }
    public static bool IsMaybeUninitType(RAST._IType tpe) {
      return (((tpe).is_TypeApp) && (object.Equals((tpe).dtor_baseName, RAST.__default.MaybeUninitPathType))) && ((new BigInteger(((tpe).dtor_arguments).Count)) == (BigInteger.One));
    }
    public static RAST._IType MaybeUninitTypeUnderlying(RAST._IType tpe) {
      return ((tpe).dtor_arguments).Select(BigInteger.Zero);
    }
    public static RAST._IExpr MaybeUninitNew(RAST._IExpr underlying) {
      return ((RAST.__default.MaybeUninitPath).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(underlying));
    }
    public static RAST._IType MaybePlaceboType(RAST._IType underlying) {
      return ((RAST.__default.MaybePlaceboPath).AsType()).Apply1(underlying);
    }
    public static Dafny.ISequence<Dafny.Rune> AddIndent(Dafny.ISequence<Dafny.Rune> raw, Dafny.ISequence<Dafny.Rune> ind)
    {
      Dafny.ISequence<Dafny.Rune> _0___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((raw).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, raw);
      } else if ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[({")).Contains((raw).Select(BigInteger.Zero))) {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in0 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in1 = Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND);
        raw = _in0;
        ind = _in1;
        goto TAIL_CALL_START;
      } else if (((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("})]")).Contains((raw).Select(BigInteger.Zero))) && ((new BigInteger((ind).Count)) > (new BigInteger(2)))) {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in2 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in3 = (ind).Take((new BigInteger((ind).Count)) - (new BigInteger(2)));
        raw = _in2;
        ind = _in3;
        goto TAIL_CALL_START;
      } else if (((raw).Select(BigInteger.Zero)) == (new Dafny.Rune('\n'))) {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)), ind));
        Dafny.ISequence<Dafny.Rune> _in4 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in5 = ind;
        raw = _in4;
        ind = _in5;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((raw).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in6 = (raw).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in7 = ind;
        raw = _in6;
        ind = _in7;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger max(BigInteger i, BigInteger j)
    {
      if ((i) < (j)) {
        return j;
      } else {
        return i;
      }
    }
    public static RAST._IExpr AssignVar(Dafny.ISequence<Dafny.Rune> name, RAST._IExpr rhs)
    {
      return RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_LocalVar(name)), rhs);
    }
    public static RAST._IExpr AssignMember(RAST._IExpr @on, Dafny.ISequence<Dafny.Rune> field, RAST._IExpr rhs)
    {
      return RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_SelectMember(@on, field)), rhs);
    }
    public static RAST._IExpr Unsafe(RAST._IExpr underlying) {
      return RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe"), underlying, DAST.Format.UnaryOpFormat.create_NoFormat());
    }
    public static RAST._IExpr MaybePlacebo(RAST._IExpr underlying) {
      return ((RAST.__default.MaybePlaceboPath).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from"))).Apply1(underlying);
    }
    public static RAST._IExpr IntoUsize(RAST._IExpr underlying) {
      return (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyUsize"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into_usize"))).Apply1(underlying);
    }
    public static bool IsBorrowUpcastBox(RAST._IExpr r) {
      RAST._IExpr _source0 = r;
      {
        if (_source0.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> op10 = _source0.dtor_op1;
          if (object.Equals(op10, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
            RAST._IExpr underlying0 = _source0.dtor_underlying;
            if (underlying0.is_Call) {
              RAST._IExpr obj0 = underlying0.dtor_obj;
              if (obj0.is_Call) {
                RAST._IExpr obj1 = obj0.dtor_obj;
                if (obj1.is_CallType) {
                  RAST._IExpr _0_name = obj1.dtor_obj;
                  Dafny.ISequence<RAST._IType> _1_targs0 = obj1.dtor_typeArguments;
                  Dafny.ISequence<RAST._IExpr> _2_args0 = obj0.dtor_arguments;
                  Dafny.ISequence<RAST._IExpr> _3_args1 = underlying0.dtor_arguments;
                  return (((object.Equals(_0_name, ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_box"))).AsExpr())) && ((new BigInteger((_2_args0).Count)).Sign == 0)) && ((new BigInteger((_3_args1).Count)) == (BigInteger.One))) && (((System.Func<bool>)(() => {
                    RAST._IExpr _source1 = (_3_args1).Select(BigInteger.Zero);
                    {
                      if (_source1.is_Call) {
                        RAST._IExpr obj2 = _source1.dtor_obj;
                        if (obj2.is_Select) {
                          RAST._IExpr obj3 = obj2.dtor_obj;
                          if (obj3.is_Identifier) {
                            Dafny.ISequence<Dafny.Rune> name0 = obj3.dtor_name;
                            if (object.Equals(name0, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
                              Dafny.ISequence<Dafny.Rune> _4_clone = obj2.dtor_name;
                              Dafny.ISequence<RAST._IExpr> _5_args2 = _source1.dtor_arguments;
                              return (new BigInteger((_5_args2).Count)).Sign == 0;
                            }
                          }
                        }
                      }
                    }
                    {
                      return false;
                    }
                  }))());
                }
              }
            }
          }
        }
      }
      {
        return false;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> DocStringPrefix { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/// ");
    } }
    public static RAST._IType SelfOwned { get {
      return (RAST.Path.create_Self()).AsType();
    } }
    public static RAST._IType SelfBorrowed { get {
      return RAST.Type.create_Borrowed(RAST.__default.SelfOwned);
    } }
    public static RAST._IType SelfBorrowedMut { get {
      return RAST.Type.create_BorrowedMut(RAST.__default.SelfOwned);
    } }
    public static RAST._IPath @global { get {
      return RAST.Path.create_Global();
    } }
    public static RAST._IPath std { get {
      return (RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"));
    } }
    public static RAST._IPath RcPath { get {
      return ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Rc"));
    } }
    public static RAST._IPath ArcPath { get {
      return ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("sync"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Arc"));
    } }
    public static RAST._IType RcType { get {
      return (RAST.__default.RcPath).AsType();
    } }
    public static RAST._IType ArcType { get {
      return (RAST.__default.ArcPath).AsType();
    } }
    public static RAST._IPath dafny__runtime { get {
      return (RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_runtime"));
    } }
    public static RAST._IPath ObjectPath { get {
      return (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"));
    } }
    public static RAST._IExpr Object { get {
      return (RAST.__default.ObjectPath).AsExpr();
    } }
    public static RAST._IPath PtrPath { get {
      return (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ptr"));
    } }
    public static RAST._IPath BoxPath { get {
      return ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("boxed"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Box"));
    } }
    public static RAST._IType BoxType { get {
      return (RAST.__default.BoxPath).AsType();
    } }
    public static RAST._IExpr Ptr { get {
      return (RAST.__default.PtrPath).AsExpr();
    } }
    public static RAST._IPath cell { get {
      return (RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cell"));
    } }
    public static RAST._IType RefcellType { get {
      return ((RAST.__default.cell).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("RefCell"))).AsType();
    } }
    public static RAST._IType CloneTrait { get {
      return (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Clone"))).AsType();
    } }
    public static RAST._IPath std__default__Default { get {
      return ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"));
    } }
    public static RAST._IType DefaultTrait { get {
      return (RAST.__default.std__default__Default).AsType();
    } }
    public static RAST._IType AnyTrait { get {
      return (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"))).AsType();
    } }
    public static RAST._IType StaticTrait { get {
      return RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'static"));
    } }
    public static RAST._IType DafnyType { get {
      return ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyType"))).AsType();
    } }
    public static RAST._IType DafnyPrint { get {
      return ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).AsType();
    } }
    public static RAST._IType DafnyTypeEq { get {
      return ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyTypeEq"))).AsType();
    } }
    public static RAST._IType Eq { get {
      return (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cmp"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Eq"))).AsType();
    } }
    public static RAST._IType Hash { get {
      return (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hash"))).AsType();
    } }
    public static RAST._IType PartialEq { get {
      return (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cmp"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PartialEq"))).AsType();
    } }
    public static RAST._IType DafnyInt { get {
      return ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).AsType();
    } }
    public static RAST._IType SyncType { get {
      return (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sync"))).AsType();
    } }
    public static RAST._IType SendType { get {
      return (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Send"))).AsType();
    } }
    public static RAST._IPath MaybeUninitPath { get {
      return ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mem"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybeUninit"));
    } }
    public static RAST._IType MaybeUninitPathType { get {
      return (RAST.__default.MaybeUninitPath).AsType();
    } }
    public static RAST._IExpr MaybeUninitExpr { get {
      return (RAST.__default.MaybeUninitPath).AsExpr();
    } }
    public static RAST._IPath MaybePlaceboPath { get {
      return (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"));
    } }
    public static Dafny.ISequence<Dafny.Rune> IND { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("    ");
    } }
    public static RAST._IExpr self { get {
      return RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"));
    } }
    public static RAST._IPath crate { get {
      return RAST.Path.create_Crate();
    } }
    public static RAST._IExpr dafny__runtime__Set { get {
      return ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set"))).AsExpr();
    } }
    public static RAST._IExpr dafny__runtime__Set__from__array { get {
      return (RAST.__default.dafny__runtime__Set).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"));
    } }
    public static RAST._IExpr dafny__runtime__Sequence { get {
      return ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsExpr();
    } }
    public static RAST._IExpr Sequence__from__array__owned { get {
      return (RAST.__default.dafny__runtime__Sequence).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array_owned"));
    } }
    public static RAST._IExpr Sequence__from__array { get {
      return (RAST.__default.dafny__runtime__Sequence).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"));
    } }
    public static RAST._IExpr dafny__runtime__Multiset { get {
      return ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset"))).AsExpr();
    } }
    public static RAST._IExpr dafny__runtime__Multiset__from__array { get {
      return (RAST.__default.dafny__runtime__Multiset).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"));
    } }
    public static RAST._IExpr std__default__Default__default { get {
      return ((RAST.__default.std__default__Default).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).Apply0();
    } }
    public static Dafny.ISequence<RAST._IAttribute> NoAttr { get {
      return Dafny.Sequence<RAST._IAttribute>.FromElements();
    } }
    public static BigInteger MAX__TUPLE__SIZE { get {
      return new BigInteger(12);
    } }
    public static Dafny.ISequence<Dafny.Rune> NoDoc { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
    } }
  }

  public interface _IRASTTopDownVisitor<T> {
    bool is_RASTTopDownVisitor { get; }
    Func<T, RAST._IType, T> dtor_VisitTypeSingle { get; }
    Func<T, RAST._IExpr, T> dtor_VisitExprSingle { get; }
    Func<T, RAST._IModDecl, RAST._IPath, T> dtor_VisitModDeclSingle { get; }
    bool dtor_recurseSubmodules { get; }
    _IRASTTopDownVisitor<__T> DowncastClone<__T>(Func<T, __T> converter0);
    T VisitMod(T acc, RAST._IMod mod, RAST._IPath SelfPath);
    T VisitTypeParams(T acc, Dafny.ISequence<RAST._ITypeParamDecl> typeParams);
    T VisitFields(T acc, RAST._IFields fields);
    T VisitModMapping(T acc, RAST._IModDecl modDecl, RAST._IPath SelfPath);
    T VisitStructMapping(T acc, RAST._IStruct @struct);
    T VisitTraitDecl(T acc, RAST._ITrait tr);
    T VisitTopFn(T acc, RAST._ITopFnDecl t);
    T VisitUse(T acc, RAST._IUse u);
    T VisitType(T acc, RAST._IType tpe);
    T VisitImplMapping(T acc, RAST._IImpl impl);
    T VisitBody(T acc, Dafny.ISequence<RAST._IImplMember> members);
    T VisitMember(T acc, RAST._IImplMember member);
    T VisitFn(T acc, RAST._IFn fn);
  }
  public class RASTTopDownVisitor<T> : _IRASTTopDownVisitor<T> {
    public readonly Func<T, RAST._IType, T> _VisitTypeSingle;
    public readonly Func<T, RAST._IExpr, T> _VisitExprSingle;
    public readonly Func<T, RAST._IModDecl, RAST._IPath, T> _VisitModDeclSingle;
    public readonly bool _recurseSubmodules;
    public RASTTopDownVisitor(Func<T, RAST._IType, T> VisitTypeSingle, Func<T, RAST._IExpr, T> VisitExprSingle, Func<T, RAST._IModDecl, RAST._IPath, T> VisitModDeclSingle, bool recurseSubmodules) {
      this._VisitTypeSingle = VisitTypeSingle;
      this._VisitExprSingle = VisitExprSingle;
      this._VisitModDeclSingle = VisitModDeclSingle;
      this._recurseSubmodules = recurseSubmodules;
    }
    public _IRASTTopDownVisitor<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IRASTTopDownVisitor<__T> dt) { return dt; }
      return new RASTTopDownVisitor<__T>((_VisitTypeSingle).DowncastClone<T, RAST._IType, T, __T, RAST._IType, __T>(Dafny.Helpers.CastConverter<__T, T>, Dafny.Helpers.Id<RAST._IType>, Dafny.Helpers.CastConverter<T, __T>), (_VisitExprSingle).DowncastClone<T, RAST._IExpr, T, __T, RAST._IExpr, __T>(Dafny.Helpers.CastConverter<__T, T>, Dafny.Helpers.Id<RAST._IExpr>, Dafny.Helpers.CastConverter<T, __T>), (_VisitModDeclSingle).DowncastClone<T, RAST._IModDecl, RAST._IPath, T, __T, RAST._IModDecl, RAST._IPath, __T>(Dafny.Helpers.CastConverter<__T, T>, Dafny.Helpers.Id<RAST._IModDecl>, Dafny.Helpers.Id<RAST._IPath>, Dafny.Helpers.CastConverter<T, __T>), _recurseSubmodules);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.RASTTopDownVisitor<T>;
      return oth != null && object.Equals(this._VisitTypeSingle, oth._VisitTypeSingle) && object.Equals(this._VisitExprSingle, oth._VisitExprSingle) && object.Equals(this._VisitModDeclSingle, oth._VisitModDeclSingle) && this._recurseSubmodules == oth._recurseSubmodules;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._VisitTypeSingle));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._VisitExprSingle));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._VisitModDeclSingle));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._recurseSubmodules));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.RASTTopDownVisitor.RASTTopDownVisitor";
      s += "(";
      s += Dafny.Helpers.ToString(this._VisitTypeSingle);
      s += ", ";
      s += Dafny.Helpers.ToString(this._VisitExprSingle);
      s += ", ";
      s += Dafny.Helpers.ToString(this._VisitModDeclSingle);
      s += ", ";
      s += Dafny.Helpers.ToString(this._recurseSubmodules);
      s += ")";
      return s;
    }
    public static RAST._IRASTTopDownVisitor<T> Default(T _default_T) {
      return create(((T x12, RAST._IType x13) => _default_T), ((T x14, RAST._IExpr x15) => _default_T), ((T x16, RAST._IModDecl x17, RAST._IPath x18) => _default_T), false);
    }
    public static Dafny.TypeDescriptor<RAST._IRASTTopDownVisitor<T>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<RAST._IRASTTopDownVisitor<T>>(RAST.RASTTopDownVisitor<T>.Default(_td_T.Default()));
    }
    public static _IRASTTopDownVisitor<T> create(Func<T, RAST._IType, T> VisitTypeSingle, Func<T, RAST._IExpr, T> VisitExprSingle, Func<T, RAST._IModDecl, RAST._IPath, T> VisitModDeclSingle, bool recurseSubmodules) {
      return new RASTTopDownVisitor<T>(VisitTypeSingle, VisitExprSingle, VisitModDeclSingle, recurseSubmodules);
    }
    public static _IRASTTopDownVisitor<T> create_RASTTopDownVisitor(Func<T, RAST._IType, T> VisitTypeSingle, Func<T, RAST._IExpr, T> VisitExprSingle, Func<T, RAST._IModDecl, RAST._IPath, T> VisitModDeclSingle, bool recurseSubmodules) {
      return create(VisitTypeSingle, VisitExprSingle, VisitModDeclSingle, recurseSubmodules);
    }
    public bool is_RASTTopDownVisitor { get { return true; } }
    public Func<T, RAST._IType, T> dtor_VisitTypeSingle {
      get {
        return this._VisitTypeSingle;
      }
    }
    public Func<T, RAST._IExpr, T> dtor_VisitExprSingle {
      get {
        return this._VisitExprSingle;
      }
    }
    public Func<T, RAST._IModDecl, RAST._IPath, T> dtor_VisitModDeclSingle {
      get {
        return this._VisitModDeclSingle;
      }
    }
    public bool dtor_recurseSubmodules {
      get {
        return this._recurseSubmodules;
      }
    }
    public T VisitMod(T acc, RAST._IMod mod, RAST._IPath SelfPath)
    {
      return (mod).Fold<T>(acc, Dafny.Helpers.Id<Func<RAST._IPath, RAST._IMod, Func<T, RAST._IModDecl, T>>>((_0_SelfPath, _1_mod) => ((System.Func<T, RAST._IModDecl, T>)((_2_acc, _3_modDecl) => {
        return (this).VisitModMapping(_2_acc, _3_modDecl, _0_SelfPath);
      })))(SelfPath, mod));
    }
    public T VisitTypeParams(T acc, Dafny.ISequence<RAST._ITypeParamDecl> typeParams)
    {
      return RAST.__default.FoldLeft<T, RAST._ITypeParamDecl>(((System.Func<T, RAST._ITypeParamDecl, T>)((_0_acc, _1_t) => {
        return RAST.__default.FoldLeft<T, RAST._IType>(((System.Func<T, RAST._IType, T>)((_2_acc, _3_t) => {
          return (this).VisitType(_2_acc, _3_t);
        })), _0_acc, (_1_t).dtor_constraints);
      })), acc, typeParams);
    }
    public T VisitFields(T acc, RAST._IFields fields)
    {
      RAST._IFields _source0 = fields;
      {
        if (_source0.is_NamedFields) {
          Dafny.ISequence<RAST._IField> _0_sFields = _source0.dtor_fields;
          return RAST.__default.FoldLeft<T, RAST._IField>(((System.Func<T, RAST._IField, T>)((_1_acc, _2_f) => {
            return (this).VisitType(_1_acc, ((_2_f).dtor_formal).dtor_tpe);
          })), acc, _0_sFields);
        }
      }
      {
        Dafny.ISequence<RAST._INamelessField> _3_sFields = _source0.dtor_types;
        return RAST.__default.FoldLeft<T, RAST._INamelessField>(((System.Func<T, RAST._INamelessField, T>)((_4_acc, _5_f) => {
          return (this).VisitType(_4_acc, (_5_f).dtor_tpe);
        })), acc, _3_sFields);
      }
    }
    public T VisitModMapping(T acc, RAST._IModDecl modDecl, RAST._IPath SelfPath)
    {
      T _0_acc = Dafny.Helpers.Id<Func<T, RAST._IModDecl, RAST._IPath, T>>((this).dtor_VisitModDeclSingle)(acc, modDecl, SelfPath);
      RAST._IModDecl _source0 = modDecl;
      {
        if (_source0.is_ModDecl) {
          RAST._IMod _1_mod = _source0.dtor_mod;
          if ((this).dtor_recurseSubmodules) {
            return (this).VisitMod(_0_acc, _1_mod, (SelfPath).MSel((_1_mod).dtor_name));
          } else {
            return _0_acc;
          }
        }
      }
      {
        if (_source0.is_StructDecl) {
          RAST._IStruct _2_struct = _source0.dtor_struct;
          return (this).VisitStructMapping(_0_acc, _2_struct);
        }
      }
      {
        if (_source0.is_TypeDecl) {
          RAST._ITypeSynonym tpe0 = _source0.dtor_tpe;
          Dafny.ISequence<Dafny.Rune> _3_attributes = tpe0.dtor_docString;
          Dafny.ISequence<Dafny.Rune> _4_name = tpe0.dtor_name;
          Dafny.ISequence<RAST._ITypeParamDecl> _5_typeParams = tpe0.dtor_typeParams;
          RAST._IType _6_tpe = tpe0.dtor_tpe;
          T _7_acc = (this).VisitTypeParams(_0_acc, _5_typeParams);
          T _8_acc = (this).VisitType(_7_acc, _6_tpe);
          return _8_acc;
        }
      }
      {
        if (_source0.is_ConstDecl) {
          RAST._IConstant c0 = _source0.dtor_c;
          Dafny.ISequence<Dafny.Rune> _9_attributes = c0.dtor_docString;
          Dafny.ISequence<Dafny.Rune> _10_name = c0.dtor_name;
          RAST._IType _11_tpe = c0.dtor_tpe;
          RAST._IExpr _12_value = c0.dtor_value;
          T _13_acc = (this).VisitType(_0_acc, _11_tpe);
          T _14_acc = (_12_value).Fold<T>(_13_acc, (this).dtor_VisitExprSingle, (this).dtor_VisitTypeSingle);
          return _14_acc;
        }
      }
      {
        if (_source0.is_EnumDecl) {
          RAST._IEnum enum0 = _source0.dtor_enum;
          Dafny.ISequence<Dafny.Rune> _15_attributes = enum0.dtor_docString;
          Dafny.ISequence<Dafny.Rune> _16_name = enum0.dtor_name;
          Dafny.ISequence<RAST._ITypeParamDecl> _17_typeParams = enum0.dtor_typeParams;
          Dafny.ISequence<RAST._IEnumCase> _18_variants = enum0.dtor_variants;
          return RAST.__default.FoldLeft<T, RAST._IEnumCase>(Dafny.Helpers.Id<Func<Dafny.ISequence<RAST._IEnumCase>, Func<T, RAST._IEnumCase, T>>>((_19_variants) => ((System.Func<T, RAST._IEnumCase, T>)((_20_acc, _21_enumCase) => {
            return (this).VisitFields(_20_acc, (_21_enumCase).dtor_fields);
          })))(_18_variants), (this).VisitTypeParams(_0_acc, _17_typeParams), _18_variants);
        }
      }
      {
        if (_source0.is_ImplDecl) {
          RAST._IImpl _22_impl = _source0.dtor_impl;
          return (this).VisitImplMapping(_0_acc, _22_impl);
        }
      }
      {
        if (_source0.is_TraitDecl) {
          RAST._ITrait _23_tr = _source0.dtor_tr;
          return (this).VisitTraitDecl(_0_acc, _23_tr);
        }
      }
      {
        if (_source0.is_TopFnDecl) {
          RAST._ITopFnDecl _24_fn = _source0.dtor_fn;
          return (this).VisitTopFn(_0_acc, _24_fn);
        }
      }
      {
        RAST._IUse _25_use = _source0.dtor_use;
        return (this).VisitUse(_0_acc, _25_use);
      }
    }
    public T VisitStructMapping(T acc, RAST._IStruct @struct)
    {
      return (this).VisitTypeParams(acc, (@struct).dtor_typeParams);
    }
    public T VisitTraitDecl(T acc, RAST._ITrait tr)
    {
      RAST._ITrait _source0 = tr;
      {
        Dafny.ISequence<RAST._ITypeParamDecl> _0_typeParams = _source0.dtor_typeParams;
        RAST._IType _1_tpe = _source0.dtor_tpe;
        Dafny.ISequence<RAST._IType> _2_parents = _source0.dtor_parents;
        Dafny.ISequence<RAST._IImplMember> _3_body = _source0.dtor_body;
        T _4_acc = (this).VisitTypeParams(acc, _0_typeParams);
        T _5_acc = (_1_tpe).Fold<T>(_4_acc, (this).dtor_VisitTypeSingle);
        T _6_acc = RAST.__default.FoldLeft<T, RAST._IType>(((System.Func<T, RAST._IType, T>)((_7_acc, _8_parent) => {
          return (_8_parent).Fold<T>(_7_acc, (this).dtor_VisitTypeSingle);
        })), _5_acc, _2_parents);
        return (this).VisitBody(_6_acc, _3_body);
      }
    }
    public T VisitTopFn(T acc, RAST._ITopFnDecl t)
    {
      RAST._ITopFnDecl _source0 = t;
      {
        Dafny.ISequence<RAST._IAttribute> _0_attributes = _source0.dtor_attributes;
        RAST._IVisibility _1_visibility = _source0.dtor_visibility;
        RAST._IFn _2_fn = _source0.dtor_fn;
        return (this).VisitFn(acc, _2_fn);
      }
    }
    public T VisitUse(T acc, RAST._IUse u)
    {
      return acc;
    }
    public T VisitType(T acc, RAST._IType tpe)
    {
      return (tpe).Fold<T>(acc, ((System.Func<T, RAST._IType, T>)((_0_acc, _1_t) => {
        return Dafny.Helpers.Id<Func<T, RAST._IType, T>>((this).dtor_VisitTypeSingle)(_0_acc, _1_t);
      })));
    }
    public T VisitImplMapping(T acc, RAST._IImpl impl)
    {
      RAST._IImpl _source0 = impl;
      {
        if (_source0.is_ImplFor) {
          Dafny.ISequence<RAST._ITypeParamDecl> _0_typeParams = _source0.dtor_typeParams;
          RAST._IType _1_tpe = _source0.dtor_tpe;
          RAST._IType _2_forType = _source0.dtor_forType;
          Dafny.ISequence<RAST._IImplMember> _3_body = _source0.dtor_body;
          T _4_acc = (this).VisitTypeParams(acc, _0_typeParams);
          T _5_acc = (this).VisitType(_4_acc, _1_tpe);
          T _6_acc = (this).VisitType(_5_acc, _2_forType);
          return (this).VisitBody(_6_acc, _3_body);
        }
      }
      {
        Dafny.ISequence<RAST._ITypeParamDecl> _7_typeParams = _source0.dtor_typeParams;
        RAST._IType _8_tpe = _source0.dtor_tpe;
        Dafny.ISequence<RAST._IImplMember> _9_body = _source0.dtor_body;
        T _10_acc = (this).VisitType(acc, _8_tpe);
        return (this).VisitBody(_10_acc, _9_body);
      }
    }
    public T VisitBody(T acc, Dafny.ISequence<RAST._IImplMember> members)
    {
      return RAST.__default.FoldLeft<T, RAST._IImplMember>(Dafny.Helpers.Id<Func<Dafny.ISequence<RAST._IImplMember>, Func<T, RAST._IImplMember, T>>>((_0_members) => ((System.Func<T, RAST._IImplMember, T>)((_1_acc, _2_member) => {
        return (this).VisitMember(_1_acc, _2_member);
      })))(members), acc, members);
    }
    public T VisitMember(T acc, RAST._IImplMember member)
    {
      RAST._IImplMember _source0 = member;
      {
        if (_source0.is_RawImplMember) {
          Dafny.ISequence<Dafny.Rune> _0_content = _source0.dtor_content;
          return acc;
        }
      }
      {
        if (_source0.is_FnDecl) {
          Dafny.ISequence<Dafny.Rune> _1_docString = _source0.dtor_docString;
          Dafny.ISequence<RAST._IAttribute> _2_attributes = _source0.dtor_attributes;
          RAST._IVisibility _3_pub = _source0.dtor_pub;
          RAST._IFn _4_fun = _source0.dtor_fun;
          return (this).VisitFn(acc, _4_fun);
        }
      }
      {
        if (_source0.is_TypeDeclMember) {
          Dafny.ISequence<Dafny.Rune> _5_name = _source0.dtor_name;
          RAST._IType _6_tpe = _source0.dtor_rhs;
          return (this).VisitType(acc, _6_tpe);
        }
      }
      {
        RAST._IExpr _7_expr = _source0.dtor_expr;
        return (_7_expr).Fold<T>(acc, (this).dtor_VisitExprSingle, (this).dtor_VisitTypeSingle);
      }
    }
    public T VisitFn(T acc, RAST._IFn fn)
    {
      RAST._IFn _source0 = fn;
      {
        Dafny.ISequence<Dafny.Rune> _0_name = _source0.dtor_name;
        Dafny.ISequence<RAST._ITypeParamDecl> _1_typeParams = _source0.dtor_typeParams;
        Dafny.ISequence<RAST._IFormal> _2_formals = _source0.dtor_formals;
        Std.Wrappers._IOption<RAST._IType> _3_returnType = _source0.dtor_returnType;
        Std.Wrappers._IOption<RAST._IExpr> _4_body = _source0.dtor_body;
        T _5_acc = (this).VisitTypeParams(acc, _1_typeParams);
        T _6_acc = RAST.__default.FoldLeft<T, RAST._IFormal>(Dafny.Helpers.Id<Func<Dafny.ISequence<RAST._IFormal>, Func<T, RAST._IFormal, T>>>((_7_formals) => ((System.Func<T, RAST._IFormal, T>)((_8_acc, _9_f) => {
          return ((_9_f).dtor_tpe).Fold<T>(_8_acc, (this).dtor_VisitTypeSingle);
        })))(_2_formals), _5_acc, _2_formals);
        T _10_acc = (((_3_returnType).is_None) ? (_6_acc) : (((_3_returnType).dtor_value).Fold<T>(_6_acc, (this).dtor_VisitTypeSingle)));
        T _11_acc = (((_4_body).is_None) ? (_10_acc) : (((_4_body).dtor_value).Fold<T>(_10_acc, (this).dtor_VisitExprSingle, (this).dtor_VisitTypeSingle)));
        return _11_acc;
      }
    }
  }

  public interface _IRASTBottomUpReplacer {
    bool is_RASTBottomUpReplacer { get; }
    Func<RAST._IMod, RAST._IPath, RAST._IMod> dtor_ReplaceModSingle { get; }
    Func<RAST._IType, RAST._IType> dtor_ReplaceTypeSingle { get; }
    Func<RAST._IExpr, RAST._IExpr> dtor_ReplaceExprSingle { get; }
    _IRASTBottomUpReplacer DowncastClone();
    RAST._IMod ReplaceMod(RAST._IMod mod, RAST._IPath SelfPath);
    RAST._IModDecl ReplaceModDecl(RAST._IModDecl modDecl, RAST._IPath SelfPath);
    RAST._IStruct ReplaceStruct(RAST._IStruct @struct);
    RAST._ITypeSynonym ReplaceTypeDecl(RAST._ITypeSynonym t);
    RAST._IConstant ReplaceConst(RAST._IConstant t);
    RAST._IEnum ReplaceEnum(RAST._IEnum @enum);
    RAST._IEnumCase ReplaceEnumCase(RAST._IEnumCase enumCase);
    RAST._IImpl ReplaceImplDecl(RAST._IImpl impl);
    RAST._ITrait ReplaceTrait(RAST._ITrait tr);
    RAST._ITopFnDecl ReplaceTopFn(RAST._ITopFnDecl t);
    RAST._IFn ReplaceFn(RAST._IFn t);
    RAST._IUse ReplaceUse(RAST._IUse use);
    Dafny.ISequence<RAST._IImplMember> ReplaceBody(Dafny.ISequence<RAST._IImplMember> decls);
    RAST._IImplMember ReplaceImplMember(RAST._IImplMember t);
    RAST._IExpr ReplaceExpr(RAST._IExpr e);
    Dafny.ISequence<RAST._ITypeParamDecl> ReplaceTypeParams(Dafny.ISequence<RAST._ITypeParamDecl> typeParams);
    RAST._IType ReplaceType(RAST._IType t);
    RAST._IFields ReplaceFields(RAST._IFields fields);
  }
  public class RASTBottomUpReplacer : _IRASTBottomUpReplacer {
    public readonly Func<RAST._IMod, RAST._IPath, RAST._IMod> _ReplaceModSingle;
    public readonly Func<RAST._IType, RAST._IType> _ReplaceTypeSingle;
    public readonly Func<RAST._IExpr, RAST._IExpr> _ReplaceExprSingle;
    public RASTBottomUpReplacer(Func<RAST._IMod, RAST._IPath, RAST._IMod> ReplaceModSingle, Func<RAST._IType, RAST._IType> ReplaceTypeSingle, Func<RAST._IExpr, RAST._IExpr> ReplaceExprSingle) {
      this._ReplaceModSingle = ReplaceModSingle;
      this._ReplaceTypeSingle = ReplaceTypeSingle;
      this._ReplaceExprSingle = ReplaceExprSingle;
    }
    public _IRASTBottomUpReplacer DowncastClone() {
      if (this is _IRASTBottomUpReplacer dt) { return dt; }
      return new RASTBottomUpReplacer(_ReplaceModSingle, _ReplaceTypeSingle, _ReplaceExprSingle);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.RASTBottomUpReplacer;
      return oth != null && object.Equals(this._ReplaceModSingle, oth._ReplaceModSingle) && object.Equals(this._ReplaceTypeSingle, oth._ReplaceTypeSingle) && object.Equals(this._ReplaceExprSingle, oth._ReplaceExprSingle);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ReplaceModSingle));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ReplaceTypeSingle));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ReplaceExprSingle));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.RASTBottomUpReplacer.RASTBottomUpReplacer";
      s += "(";
      s += Dafny.Helpers.ToString(this._ReplaceModSingle);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ReplaceTypeSingle);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ReplaceExprSingle);
      s += ")";
      return s;
    }
    private static readonly RAST._IRASTBottomUpReplacer theDefault = create(((Func<RAST._IMod, RAST._IPath, RAST._IMod>)null), ((RAST._IType x19) => RAST.Type.Default()), ((RAST._IExpr x20) => RAST.Expr.Default()));
    public static RAST._IRASTBottomUpReplacer Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IRASTBottomUpReplacer> _TYPE = new Dafny.TypeDescriptor<RAST._IRASTBottomUpReplacer>(RAST.RASTBottomUpReplacer.Default());
    public static Dafny.TypeDescriptor<RAST._IRASTBottomUpReplacer> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IRASTBottomUpReplacer create(Func<RAST._IMod, RAST._IPath, RAST._IMod> ReplaceModSingle, Func<RAST._IType, RAST._IType> ReplaceTypeSingle, Func<RAST._IExpr, RAST._IExpr> ReplaceExprSingle) {
      return new RASTBottomUpReplacer(ReplaceModSingle, ReplaceTypeSingle, ReplaceExprSingle);
    }
    public static _IRASTBottomUpReplacer create_RASTBottomUpReplacer(Func<RAST._IMod, RAST._IPath, RAST._IMod> ReplaceModSingle, Func<RAST._IType, RAST._IType> ReplaceTypeSingle, Func<RAST._IExpr, RAST._IExpr> ReplaceExprSingle) {
      return create(ReplaceModSingle, ReplaceTypeSingle, ReplaceExprSingle);
    }
    public bool is_RASTBottomUpReplacer { get { return true; } }
    public Func<RAST._IMod, RAST._IPath, RAST._IMod> dtor_ReplaceModSingle {
      get {
        return this._ReplaceModSingle;
      }
    }
    public Func<RAST._IType, RAST._IType> dtor_ReplaceTypeSingle {
      get {
        return this._ReplaceTypeSingle;
      }
    }
    public Func<RAST._IExpr, RAST._IExpr> dtor_ReplaceExprSingle {
      get {
        return this._ReplaceExprSingle;
      }
    }
    public RAST._IMod ReplaceMod(RAST._IMod mod, RAST._IPath SelfPath)
    {
      if ((mod).is_ExternMod) {
        return mod;
      } else {
        Dafny.ISequence<RAST._IModDecl> _0_newModDeclarations = (mod).Fold<Dafny.ISequence<RAST._IModDecl>>(Dafny.Sequence<RAST._IModDecl>.FromElements(), Dafny.Helpers.Id<Func<RAST._IPath, RAST._IMod, Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>>>((_1_SelfPath, _2_mod) => ((System.Func<Dafny.ISequence<RAST._IModDecl>, RAST._IModDecl, Dafny.ISequence<RAST._IModDecl>>)((_3_current, _4_modDecl) => {
          return Dafny.Sequence<RAST._IModDecl>.Concat(_3_current, Dafny.Sequence<RAST._IModDecl>.FromElements((this).ReplaceModDecl(_4_modDecl, _1_SelfPath)));
        })))(SelfPath, mod));
        RAST._IMod _5_dt__update__tmp_h0 = mod;
        Dafny.ISequence<RAST._IModDecl> _6_dt__update_hbody_h0 = _0_newModDeclarations;
        return RAST.Mod.create_Mod((_5_dt__update__tmp_h0).dtor_docString, (_5_dt__update__tmp_h0).dtor_attributes, (_5_dt__update__tmp_h0).dtor_name, _6_dt__update_hbody_h0);
      }
    }
    public RAST._IModDecl ReplaceModDecl(RAST._IModDecl modDecl, RAST._IPath SelfPath)
    {
      RAST._IModDecl _source0 = modDecl;
      {
        if (_source0.is_ModDecl) {
          RAST._IMod _0_mod = _source0.dtor_mod;
          return RAST.ModDecl.create_ModDecl(Dafny.Helpers.Id<Func<RAST._IMod, RAST._IPath, RAST._IMod>>((this).dtor_ReplaceModSingle)(_0_mod, (SelfPath).MSel((_0_mod).dtor_name)));
        }
      }
      {
        if (_source0.is_StructDecl) {
          RAST._IStruct _1_struct = _source0.dtor_struct;
          return RAST.ModDecl.create_StructDecl((this).ReplaceStruct(_1_struct));
        }
      }
      {
        if (_source0.is_TypeDecl) {
          RAST._ITypeSynonym _2_tpe = _source0.dtor_tpe;
          return RAST.ModDecl.create_TypeDecl((this).ReplaceTypeDecl(_2_tpe));
        }
      }
      {
        if (_source0.is_ConstDecl) {
          RAST._IConstant _3_c = _source0.dtor_c;
          return RAST.ModDecl.create_ConstDecl((this).ReplaceConst(_3_c));
        }
      }
      {
        if (_source0.is_EnumDecl) {
          RAST._IEnum _4_enum = _source0.dtor_enum;
          return RAST.ModDecl.create_EnumDecl((this).ReplaceEnum(_4_enum));
        }
      }
      {
        if (_source0.is_ImplDecl) {
          RAST._IImpl _5_impl = _source0.dtor_impl;
          return RAST.ModDecl.create_ImplDecl((this).ReplaceImplDecl(_5_impl));
        }
      }
      {
        if (_source0.is_TraitDecl) {
          RAST._ITrait _6_tr = _source0.dtor_tr;
          return RAST.ModDecl.create_TraitDecl((this).ReplaceTrait(_6_tr));
        }
      }
      {
        if (_source0.is_TopFnDecl) {
          RAST._ITopFnDecl _7_fn = _source0.dtor_fn;
          return RAST.ModDecl.create_TopFnDecl((this).ReplaceTopFn(_7_fn));
        }
      }
      {
        RAST._IUse _8_use = _source0.dtor_use;
        return RAST.ModDecl.create_UseDecl((this).ReplaceUse(_8_use));
      }
    }
    public RAST._IStruct ReplaceStruct(RAST._IStruct @struct) {
      RAST._IStruct _source0 = @struct;
      {
        Dafny.ISequence<Dafny.Rune> _0_docString = _source0.dtor_docString;
        Dafny.ISequence<RAST._IAttribute> _1_attributes = _source0.dtor_attributes;
        Dafny.ISequence<Dafny.Rune> _2_name = _source0.dtor_name;
        Dafny.ISequence<RAST._ITypeParamDecl> _3_typeParams = _source0.dtor_typeParams;
        RAST._IFields _4_fields = _source0.dtor_fields;
        return RAST.Struct.create(_0_docString, _1_attributes, _2_name, (this).ReplaceTypeParams(_3_typeParams), (this).ReplaceFields(_4_fields));
      }
    }
    public RAST._ITypeSynonym ReplaceTypeDecl(RAST._ITypeSynonym t) {
      RAST._ITypeSynonym _source0 = t;
      {
        Dafny.ISequence<Dafny.Rune> _0_docString = _source0.dtor_docString;
        Dafny.ISequence<RAST._IAttribute> _1_attributes = _source0.dtor_attributes;
        Dafny.ISequence<Dafny.Rune> _2_name = _source0.dtor_name;
        Dafny.ISequence<RAST._ITypeParamDecl> _3_typeParams = _source0.dtor_typeParams;
        RAST._IType _4_tpe = _source0.dtor_tpe;
        return RAST.TypeSynonym.create(_0_docString, _1_attributes, _2_name, (this).ReplaceTypeParams(_3_typeParams), (this).ReplaceType(_4_tpe));
      }
    }
    public RAST._IConstant ReplaceConst(RAST._IConstant t) {
      RAST._IConstant _source0 = t;
      {
        Dafny.ISequence<Dafny.Rune> _0_docString = _source0.dtor_docString;
        Dafny.ISequence<RAST._IAttribute> _1_attributes = _source0.dtor_attributes;
        Dafny.ISequence<Dafny.Rune> _2_name = _source0.dtor_name;
        RAST._IType _3_tpe = _source0.dtor_tpe;
        RAST._IExpr _4_value = _source0.dtor_value;
        return RAST.Constant.create(_0_docString, _1_attributes, _2_name, (this).ReplaceType(_3_tpe), (this).ReplaceExpr(_4_value));
      }
    }
    public RAST._IEnum ReplaceEnum(RAST._IEnum @enum) {
      RAST._IEnum _source0 = @enum;
      {
        Dafny.ISequence<Dafny.Rune> _0_docString = _source0.dtor_docString;
        Dafny.ISequence<RAST._IAttribute> _1_attributes = _source0.dtor_attributes;
        Dafny.ISequence<Dafny.Rune> _2_name = _source0.dtor_name;
        Dafny.ISequence<RAST._ITypeParamDecl> _3_typeParams = _source0.dtor_typeParams;
        Dafny.ISequence<RAST._IEnumCase> _4_variants = _source0.dtor_variants;
        return RAST.Enum.create(_0_docString, _1_attributes, _2_name, (this).ReplaceTypeParams(_3_typeParams), Std.Collections.Seq.__default.Map<RAST._IEnumCase, RAST._IEnumCase>(((System.Func<RAST._IEnumCase, RAST._IEnumCase>)((_5_t) => {
  return (this).ReplaceEnumCase(_5_t);
})), _4_variants));
      }
    }
    public RAST._IEnumCase ReplaceEnumCase(RAST._IEnumCase enumCase) {
      RAST._IEnumCase _source0 = enumCase;
      {
        Dafny.ISequence<Dafny.Rune> _0_docString = _source0.dtor_docString;
        Dafny.ISequence<Dafny.Rune> _1_name = _source0.dtor_name;
        RAST._IFields _2_fields = _source0.dtor_fields;
        return RAST.EnumCase.create(_0_docString, _1_name, (this).ReplaceFields(_2_fields));
      }
    }
    public RAST._IImpl ReplaceImplDecl(RAST._IImpl impl) {
      RAST._IImpl _source0 = impl;
      {
        if (_source0.is_ImplFor) {
          Dafny.ISequence<RAST._ITypeParamDecl> _0_typeParams = _source0.dtor_typeParams;
          RAST._IType _1_tpe = _source0.dtor_tpe;
          RAST._IType _2_forType = _source0.dtor_forType;
          Dafny.ISequence<RAST._IImplMember> _3_body = _source0.dtor_body;
          return RAST.Impl.create_ImplFor((this).ReplaceTypeParams(_0_typeParams), (this).ReplaceType(_1_tpe), (this).ReplaceType(_2_forType), (this).ReplaceBody(_3_body));
        }
      }
      {
        Dafny.ISequence<RAST._ITypeParamDecl> _4_typeParams = _source0.dtor_typeParams;
        RAST._IType _5_tpe = _source0.dtor_tpe;
        Dafny.ISequence<RAST._IImplMember> _6_body = _source0.dtor_body;
        return RAST.Impl.create_Impl((this).ReplaceTypeParams(_4_typeParams), (this).ReplaceType(_5_tpe), (this).ReplaceBody(_6_body));
      }
    }
    public RAST._ITrait ReplaceTrait(RAST._ITrait tr) {
      RAST._ITrait _source0 = tr;
      {
        Dafny.ISequence<Dafny.Rune> _0_docString = _source0.dtor_docString;
        Dafny.ISequence<RAST._IAttribute> _1_attributes = _source0.dtor_attributes;
        Dafny.ISequence<RAST._ITypeParamDecl> _2_typeParams = _source0.dtor_typeParams;
        RAST._IType _3_tpe = _source0.dtor_tpe;
        Dafny.ISequence<RAST._IType> _4_parents = _source0.dtor_parents;
        Dafny.ISequence<RAST._IImplMember> _5_body = _source0.dtor_body;
        return RAST.Trait.create(_0_docString, _1_attributes, (this).ReplaceTypeParams(_2_typeParams), (this).ReplaceType(_3_tpe), Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(((System.Func<RAST._IType, RAST._IType>)((_6_t) => {
  return (this).ReplaceType(_6_t);
})), _4_parents), (this).ReplaceBody(_5_body));
      }
    }
    public RAST._ITopFnDecl ReplaceTopFn(RAST._ITopFnDecl t) {
      RAST._ITopFnDecl _source0 = t;
      {
        Dafny.ISequence<Dafny.Rune> _0_docString = _source0.dtor_docString;
        Dafny.ISequence<RAST._IAttribute> _1_attributes = _source0.dtor_attributes;
        RAST._IVisibility _2_visibility = _source0.dtor_visibility;
        RAST._IFn _3_fn = _source0.dtor_fn;
        return RAST.TopFnDecl.create(_0_docString, _1_attributes, _2_visibility, (this).ReplaceFn(_3_fn));
      }
    }
    public RAST._IFn ReplaceFn(RAST._IFn t) {
      RAST._IFn _source0 = t;
      {
        Dafny.ISequence<Dafny.Rune> _0_name = _source0.dtor_name;
        Dafny.ISequence<RAST._ITypeParamDecl> _1_typeParams = _source0.dtor_typeParams;
        Dafny.ISequence<RAST._IFormal> _2_formals = _source0.dtor_formals;
        Std.Wrappers._IOption<RAST._IType> _3_returnType = _source0.dtor_returnType;
        Std.Wrappers._IOption<RAST._IExpr> _4_body = _source0.dtor_body;
        return RAST.Fn.create(_0_name, (this).ReplaceTypeParams(_1_typeParams), Std.Collections.Seq.__default.Map<RAST._IFormal, RAST._IFormal>(Dafny.Helpers.Id<Func<Dafny.ISequence<RAST._IFormal>, Func<RAST._IFormal, RAST._IFormal>>>((_5_formals) => ((System.Func<RAST._IFormal, RAST._IFormal>)((_6_f) => {
  return (_6_f).Replace(this.ReplaceType);
})))(_2_formals), _2_formals), (((_3_returnType).is_None) ? (Std.Wrappers.Option<RAST._IType>.create_None()) : (Std.Wrappers.Option<RAST._IType>.create_Some(((_3_returnType).dtor_value).Replace(this.ReplaceType)))), (((_4_body).is_None) ? (Std.Wrappers.Option<RAST._IExpr>.create_None()) : (Std.Wrappers.Option<RAST._IExpr>.create_Some(((_4_body).dtor_value).Replace(this.ReplaceExpr, this.ReplaceType)))));
      }
    }
    public RAST._IUse ReplaceUse(RAST._IUse use) {
      RAST._IUse _source0 = use;
      {
        RAST._IVisibility _0_visibility = _source0.dtor_visibility;
        RAST._IPath _1_path = _source0.dtor_path;
        return RAST.Use.create(_0_visibility, _1_path);
      }
    }
    public Dafny.ISequence<RAST._IImplMember> ReplaceBody(Dafny.ISequence<RAST._IImplMember> decls) {
      return Std.Collections.Seq.__default.Map<RAST._IImplMember, RAST._IImplMember>(((System.Func<RAST._IImplMember, RAST._IImplMember>)((_0_t) => {
        return (this).ReplaceImplMember(_0_t);
      })), decls);
    }
    public RAST._IImplMember ReplaceImplMember(RAST._IImplMember t) {
      RAST._IImplMember _source0 = t;
      {
        if (_source0.is_RawImplMember) {
          Dafny.ISequence<Dafny.Rune> _0_content = _source0.dtor_content;
          return t;
        }
      }
      {
        if (_source0.is_FnDecl) {
          Dafny.ISequence<Dafny.Rune> _1_docString = _source0.dtor_docString;
          Dafny.ISequence<RAST._IAttribute> _2_attributes = _source0.dtor_attributes;
          RAST._IVisibility _3_pub = _source0.dtor_pub;
          RAST._IFn _4_fun = _source0.dtor_fun;
          return RAST.ImplMember.create_FnDecl(_1_docString, _2_attributes, _3_pub, (this).ReplaceFn(_4_fun));
        }
      }
      {
        if (_source0.is_TypeDeclMember) {
          Dafny.ISequence<Dafny.Rune> _5_name = _source0.dtor_name;
          RAST._IType _6_tpe = _source0.dtor_rhs;
          return RAST.ImplMember.create_TypeDeclMember(_5_name, (this).ReplaceType(_6_tpe));
        }
      }
      {
        RAST._IExpr _7_expr = _source0.dtor_expr;
        return RAST.ImplMember.create_ImplMemberMacro((this).ReplaceExpr(_7_expr));
      }
    }
    public RAST._IExpr ReplaceExpr(RAST._IExpr e) {
      return (e).Replace((this).dtor_ReplaceExprSingle, (this).dtor_ReplaceTypeSingle);
    }
    public Dafny.ISequence<RAST._ITypeParamDecl> ReplaceTypeParams(Dafny.ISequence<RAST._ITypeParamDecl> typeParams) {
      return Std.Collections.Seq.__default.Map<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(((System.Func<RAST._ITypeParamDecl, RAST._ITypeParamDecl>)((_0_t) => {
        return Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_0_t, _pat_let52_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let52_0, _1_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(((System.Func<RAST._IType, RAST._IType>)((_2_constraint) => {
          return (this).ReplaceType(_2_constraint);
        })), (_0_t).dtor_constraints), _pat_let53_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let53_0, _3_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1_dt__update__tmp_h0).dtor_name, _3_dt__update_hconstraints_h0)))));
      })), typeParams);
    }
    public RAST._IType ReplaceType(RAST._IType t) {
      return (t).Replace((this).dtor_ReplaceTypeSingle);
    }
    public RAST._IFields ReplaceFields(RAST._IFields fields) {
      RAST._IFields _source0 = fields;
      {
        if (_source0.is_NamedFields) {
          Dafny.ISequence<RAST._IField> _0_sFields = _source0.dtor_fields;
          return RAST.Fields.create_NamedFields(Std.Collections.Seq.__default.Map<RAST._IField, RAST._IField>(((System.Func<RAST._IField, RAST._IField>)((_1_f) => {
  return Dafny.Helpers.Let<RAST._IField, RAST._IField>(_1_f, _pat_let54_0 => Dafny.Helpers.Let<RAST._IField, RAST._IField>(_pat_let54_0, _2_dt__update__tmp_h1 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>((_1_f).dtor_formal, _pat_let56_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IFormal>(_pat_let56_0, _3_dt__update__tmp_h0 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>((this).ReplaceType(((_1_f).dtor_formal).dtor_tpe), _pat_let57_0 => Dafny.Helpers.Let<RAST._IType, RAST._IFormal>(_pat_let57_0, _4_dt__update_htpe_h0 => RAST.Formal.create((_3_dt__update__tmp_h0).dtor_name, _4_dt__update_htpe_h0))))), _pat_let55_0 => Dafny.Helpers.Let<RAST._IFormal, RAST._IField>(_pat_let55_0, _5_dt__update_hformal_h0 => RAST.Field.create((_2_dt__update__tmp_h1).dtor_visibility, _5_dt__update_hformal_h0)))));
})), _0_sFields));
        }
      }
      {
        Dafny.ISequence<RAST._INamelessField> _6_sFields = _source0.dtor_types;
        return RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._INamelessField, RAST._INamelessField>(((System.Func<RAST._INamelessField, RAST._INamelessField>)((_7_f) => {
  return Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_7_f, _pat_let58_0 => Dafny.Helpers.Let<RAST._INamelessField, RAST._INamelessField>(_pat_let58_0, _8_dt__update__tmp_h2 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>((this).ReplaceType((_7_f).dtor_tpe), _pat_let59_0 => Dafny.Helpers.Let<RAST._IType, RAST._INamelessField>(_pat_let59_0, _9_dt__update_htpe_h1 => RAST.NamelessField.create((_8_dt__update__tmp_h2).dtor_visibility, _9_dt__update_htpe_h1)))));
})), _6_sFields));
      }
    }
  }

  public interface _IMod {
    bool is_Mod { get; }
    bool is_ExternMod { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<RAST._IAttribute> dtor_attributes { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<RAST._IModDecl> dtor_body { get; }
    _IMod DowncastClone();
    __T Fold<__T>(__T acc, Func<__T, RAST._IModDecl, __T> accBuilder);
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public abstract class Mod : _IMod {
    public Mod() {
    }
    private static readonly RAST._IMod theDefault = create_Mod(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IAttribute>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IModDecl>.Empty);
    public static RAST._IMod Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IMod> _TYPE = new Dafny.TypeDescriptor<RAST._IMod>(RAST.Mod.Default());
    public static Dafny.TypeDescriptor<RAST._IMod> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMod create_Mod(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._IModDecl> body) {
      return new Mod_Mod(docString, attributes, name, body);
    }
    public static _IMod create_ExternMod(Dafny.ISequence<Dafny.Rune> name) {
      return new Mod_ExternMod(name);
    }
    public bool is_Mod { get { return this is Mod_Mod; } }
    public bool is_ExternMod { get { return this is Mod_ExternMod; } }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        var d = this;
        return ((Mod_Mod)d)._docString;
      }
    }
    public Dafny.ISequence<RAST._IAttribute> dtor_attributes {
      get {
        var d = this;
        return ((Mod_Mod)d)._attributes;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        if (d is Mod_Mod) { return ((Mod_Mod)d)._name; }
        return ((Mod_ExternMod)d)._name;
      }
    }
    public Dafny.ISequence<RAST._IModDecl> dtor_body {
      get {
        var d = this;
        return ((Mod_Mod)d)._body;
      }
    }
    public abstract _IMod DowncastClone();
    public __T Fold<__T>(__T acc, Func<__T, RAST._IModDecl, __T> accBuilder)
    {
      if ((this).is_ExternMod) {
        return acc;
      } else {
        return RAST.__default.FoldLeft<__T, RAST._IModDecl>(accBuilder, acc, (this).dtor_body);
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      var _pat_let_tv0 = ind;
      var _pat_let_tv1 = ind;
      var _pat_let_tv2 = ind;
      var _pat_let_tv3 = ind;
      var _pat_let_tv4 = ind;
      var _pat_let_tv5 = ind;
      RAST._IMod _source0 = this;
      {
        if (_source0.is_ExternMod) {
          Dafny.ISequence<Dafny.Rune> _0_name = _source0.dtor_name;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub mod "), _0_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      }
      {
        Dafny.ISequence<Dafny.Rune> _1_docString = _source0.dtor_docString;
        Dafny.ISequence<RAST._IAttribute> _2_attributes = _source0.dtor_attributes;
        Dafny.ISequence<Dafny.Rune> _3_name = _source0.dtor_name;
        Dafny.ISequence<RAST._IModDecl> _4_body = _source0.dtor_body;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.ToDocstringPrefix(_1_docString, ind), RAST.Attribute.ToStringMultiple(_2_attributes, ind)), Dafny.Helpers.Let<bool, Dafny.ISequence<Dafny.Rune>>(((new BigInteger((_4_body).Count)).Sign == 1) && (((_4_body).Select(BigInteger.Zero)).is_UseDecl), _pat_let60_0 => Dafny.Helpers.Let<bool, Dafny.ISequence<Dafny.Rune>>(_pat_let60_0, _5_startWithUse => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((_5_startWithUse) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _pat_let_tv0), RAST.__default.IND)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _pat_let61_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let61_0, _6_prefixIfNotUseDecl => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((_5_startWithUse) ? (Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv1, RAST.__default.IND)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), _pat_let62_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let62_0, _7_prefixIfUseDecl => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((_5_startWithUse) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n\n"), _pat_let_tv2), RAST.__default.IND))), _pat_let63_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let63_0, _8_infixDecl => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((_5_startWithUse) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(_pat_let_tv3, RAST.__default.IND))), _pat_let64_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let64_0, _9_initialIdent => Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub mod "), _3_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _9_initialIdent), RAST.__default.SeqToString<RAST._IModDecl>(_4_body, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>, Func<RAST._IModDecl, Dafny.ISequence<Dafny.Rune>>>>((_10_prefixIfUseDecl, _11_prefixIfNotUseDecl, _12_ind) => ((System.Func<RAST._IModDecl, Dafny.ISequence<Dafny.Rune>>)((_13_modDecl) => {
          return Dafny.Sequence<Dafny.Rune>.Concat((((_13_modDecl).is_UseDecl) ? (_10_prefixIfUseDecl) : (_11_prefixIfNotUseDecl)), (_13_modDecl)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_12_ind, RAST.__default.IND)));
        })))(_7_prefixIfUseDecl, _6_prefixIfNotUseDecl, _pat_let_tv4), _8_infixDecl)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _pat_let_tv5), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))))))))))));
      }
    }
  }
  public class Mod_Mod : Mod {
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<RAST._IAttribute> _attributes;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._IModDecl> _body;
    public Mod_Mod(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._IModDecl> body) : base() {
      this._docString = docString;
      this._attributes = attributes;
      this._name = name;
      this._body = body;
    }
    public override _IMod DowncastClone() {
      if (this is _IMod dt) { return dt; }
      return new Mod_Mod(_docString, _attributes, _name, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Mod_Mod;
      return oth != null && object.Equals(this._docString, oth._docString) && object.Equals(this._attributes, oth._attributes) && object.Equals(this._name, oth._name) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Mod.Mod";
      s += "(";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }
  public class Mod_ExternMod : Mod {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public Mod_ExternMod(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._name = name;
    }
    public override _IMod DowncastClone() {
      if (this is _IMod dt) { return dt; }
      return new Mod_ExternMod(_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Mod_ExternMod;
      return oth != null && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Mod.ExternMod";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }

  public interface _IModDecl {
    bool is_ModDecl { get; }
    bool is_StructDecl { get; }
    bool is_TypeDecl { get; }
    bool is_ConstDecl { get; }
    bool is_EnumDecl { get; }
    bool is_ImplDecl { get; }
    bool is_TraitDecl { get; }
    bool is_TopFnDecl { get; }
    bool is_UseDecl { get; }
    RAST._IMod dtor_mod { get; }
    RAST._IStruct dtor_struct { get; }
    RAST._ITypeSynonym dtor_tpe { get; }
    RAST._IConstant dtor_c { get; }
    RAST._IEnum dtor_enum { get; }
    RAST._IImpl dtor_impl { get; }
    RAST._ITrait dtor_tr { get; }
    RAST._ITopFnDecl dtor_fn { get; }
    RAST._IUse dtor_use { get; }
    _IModDecl DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public abstract class ModDecl : _IModDecl {
    public ModDecl() {
    }
    private static readonly RAST._IModDecl theDefault = create_ModDecl(RAST.Mod.Default());
    public static RAST._IModDecl Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IModDecl> _TYPE = new Dafny.TypeDescriptor<RAST._IModDecl>(RAST.ModDecl.Default());
    public static Dafny.TypeDescriptor<RAST._IModDecl> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IModDecl create_ModDecl(RAST._IMod mod) {
      return new ModDecl_ModDecl(mod);
    }
    public static _IModDecl create_StructDecl(RAST._IStruct @struct) {
      return new ModDecl_StructDecl(@struct);
    }
    public static _IModDecl create_TypeDecl(RAST._ITypeSynonym tpe) {
      return new ModDecl_TypeDecl(tpe);
    }
    public static _IModDecl create_ConstDecl(RAST._IConstant c) {
      return new ModDecl_ConstDecl(c);
    }
    public static _IModDecl create_EnumDecl(RAST._IEnum @enum) {
      return new ModDecl_EnumDecl(@enum);
    }
    public static _IModDecl create_ImplDecl(RAST._IImpl impl) {
      return new ModDecl_ImplDecl(impl);
    }
    public static _IModDecl create_TraitDecl(RAST._ITrait tr) {
      return new ModDecl_TraitDecl(tr);
    }
    public static _IModDecl create_TopFnDecl(RAST._ITopFnDecl fn) {
      return new ModDecl_TopFnDecl(fn);
    }
    public static _IModDecl create_UseDecl(RAST._IUse use) {
      return new ModDecl_UseDecl(use);
    }
    public bool is_ModDecl { get { return this is ModDecl_ModDecl; } }
    public bool is_StructDecl { get { return this is ModDecl_StructDecl; } }
    public bool is_TypeDecl { get { return this is ModDecl_TypeDecl; } }
    public bool is_ConstDecl { get { return this is ModDecl_ConstDecl; } }
    public bool is_EnumDecl { get { return this is ModDecl_EnumDecl; } }
    public bool is_ImplDecl { get { return this is ModDecl_ImplDecl; } }
    public bool is_TraitDecl { get { return this is ModDecl_TraitDecl; } }
    public bool is_TopFnDecl { get { return this is ModDecl_TopFnDecl; } }
    public bool is_UseDecl { get { return this is ModDecl_UseDecl; } }
    public RAST._IMod dtor_mod {
      get {
        var d = this;
        return ((ModDecl_ModDecl)d)._mod;
      }
    }
    public RAST._IStruct dtor_struct {
      get {
        var d = this;
        return ((ModDecl_StructDecl)d)._struct;
      }
    }
    public RAST._ITypeSynonym dtor_tpe {
      get {
        var d = this;
        return ((ModDecl_TypeDecl)d)._tpe;
      }
    }
    public RAST._IConstant dtor_c {
      get {
        var d = this;
        return ((ModDecl_ConstDecl)d)._c;
      }
    }
    public RAST._IEnum dtor_enum {
      get {
        var d = this;
        return ((ModDecl_EnumDecl)d)._enum;
      }
    }
    public RAST._IImpl dtor_impl {
      get {
        var d = this;
        return ((ModDecl_ImplDecl)d)._impl;
      }
    }
    public RAST._ITrait dtor_tr {
      get {
        var d = this;
        return ((ModDecl_TraitDecl)d)._tr;
      }
    }
    public RAST._ITopFnDecl dtor_fn {
      get {
        var d = this;
        return ((ModDecl_TopFnDecl)d)._fn;
      }
    }
    public RAST._IUse dtor_use {
      get {
        var d = this;
        return ((ModDecl_UseDecl)d)._use;
      }
    }
    public abstract _IModDecl DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      if ((this).is_ModDecl) {
        return ((this).dtor_mod)._ToString(ind);
      } else if ((this).is_StructDecl) {
        return ((this).dtor_struct)._ToString(ind);
      } else if ((this).is_ImplDecl) {
        return ((this).dtor_impl)._ToString(ind);
      } else if ((this).is_EnumDecl) {
        return ((this).dtor_enum)._ToString(ind);
      } else if ((this).is_TypeDecl) {
        return ((this).dtor_tpe)._ToString(ind);
      } else if ((this).is_ConstDecl) {
        return ((this).dtor_c)._ToString(ind);
      } else if ((this).is_TraitDecl) {
        return ((this).dtor_tr)._ToString(ind);
      } else if ((this).is_TopFnDecl) {
        return ((this).dtor_fn)._ToString(ind);
      } else {
        return ((this).dtor_use)._ToString(ind);
      }
    }
  }
  public class ModDecl_ModDecl : ModDecl {
    public readonly RAST._IMod _mod;
    public ModDecl_ModDecl(RAST._IMod mod) : base() {
      this._mod = mod;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_ModDecl(_mod);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_ModDecl;
      return oth != null && object.Equals(this._mod, oth._mod);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._mod));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.ModDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._mod);
      s += ")";
      return s;
    }
  }
  public class ModDecl_StructDecl : ModDecl {
    public readonly RAST._IStruct _struct;
    public ModDecl_StructDecl(RAST._IStruct @struct) : base() {
      this._struct = @struct;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_StructDecl(_struct);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_StructDecl;
      return oth != null && object.Equals(this._struct, oth._struct);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._struct));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.StructDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._struct);
      s += ")";
      return s;
    }
  }
  public class ModDecl_TypeDecl : ModDecl {
    public readonly RAST._ITypeSynonym _tpe;
    public ModDecl_TypeDecl(RAST._ITypeSynonym tpe) : base() {
      this._tpe = tpe;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_TypeDecl(_tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_TypeDecl;
      return oth != null && object.Equals(this._tpe, oth._tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.TypeDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ")";
      return s;
    }
  }
  public class ModDecl_ConstDecl : ModDecl {
    public readonly RAST._IConstant _c;
    public ModDecl_ConstDecl(RAST._IConstant c) : base() {
      this._c = c;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_ConstDecl(_c);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_ConstDecl;
      return oth != null && object.Equals(this._c, oth._c);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._c));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.ConstDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._c);
      s += ")";
      return s;
    }
  }
  public class ModDecl_EnumDecl : ModDecl {
    public readonly RAST._IEnum _enum;
    public ModDecl_EnumDecl(RAST._IEnum @enum) : base() {
      this._enum = @enum;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_EnumDecl(_enum);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_EnumDecl;
      return oth != null && object.Equals(this._enum, oth._enum);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._enum));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.EnumDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._enum);
      s += ")";
      return s;
    }
  }
  public class ModDecl_ImplDecl : ModDecl {
    public readonly RAST._IImpl _impl;
    public ModDecl_ImplDecl(RAST._IImpl impl) : base() {
      this._impl = impl;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_ImplDecl(_impl);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_ImplDecl;
      return oth != null && object.Equals(this._impl, oth._impl);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._impl));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.ImplDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._impl);
      s += ")";
      return s;
    }
  }
  public class ModDecl_TraitDecl : ModDecl {
    public readonly RAST._ITrait _tr;
    public ModDecl_TraitDecl(RAST._ITrait tr) : base() {
      this._tr = tr;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_TraitDecl(_tr);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_TraitDecl;
      return oth != null && object.Equals(this._tr, oth._tr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.TraitDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._tr);
      s += ")";
      return s;
    }
  }
  public class ModDecl_TopFnDecl : ModDecl {
    public readonly RAST._ITopFnDecl _fn;
    public ModDecl_TopFnDecl(RAST._ITopFnDecl fn) : base() {
      this._fn = fn;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_TopFnDecl(_fn);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_TopFnDecl;
      return oth != null && object.Equals(this._fn, oth._fn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.TopFnDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._fn);
      s += ")";
      return s;
    }
  }
  public class ModDecl_UseDecl : ModDecl {
    public readonly RAST._IUse _use;
    public ModDecl_UseDecl(RAST._IUse use) : base() {
      this._use = use;
    }
    public override _IModDecl DowncastClone() {
      if (this is _IModDecl dt) { return dt; }
      return new ModDecl_UseDecl(_use);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ModDecl_UseDecl;
      return oth != null && object.Equals(this._use, oth._use);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._use));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ModDecl.UseDecl";
      s += "(";
      s += Dafny.Helpers.ToString(this._use);
      s += ")";
      return s;
    }
  }

  public interface _IUse {
    bool is_Use { get; }
    RAST._IVisibility dtor_visibility { get; }
    RAST._IPath dtor_path { get; }
    _IUse DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Use : _IUse {
    public readonly RAST._IVisibility _visibility;
    public readonly RAST._IPath _path;
    public Use(RAST._IVisibility visibility, RAST._IPath path) {
      this._visibility = visibility;
      this._path = path;
    }
    public _IUse DowncastClone() {
      if (this is _IUse dt) { return dt; }
      return new Use(_visibility, _path);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Use;
      return oth != null && object.Equals(this._visibility, oth._visibility) && object.Equals(this._path, oth._path);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._visibility));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._path));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Use.Use";
      s += "(";
      s += Dafny.Helpers.ToString(this._visibility);
      s += ", ";
      s += Dafny.Helpers.ToString(this._path);
      s += ")";
      return s;
    }
    private static readonly RAST._IUse theDefault = create(RAST.Visibility.Default(), RAST.Path.Default());
    public static RAST._IUse Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IUse> _TYPE = new Dafny.TypeDescriptor<RAST._IUse>(RAST.Use.Default());
    public static Dafny.TypeDescriptor<RAST._IUse> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUse create(RAST._IVisibility visibility, RAST._IPath path) {
      return new Use(visibility, path);
    }
    public static _IUse create_Use(RAST._IVisibility visibility, RAST._IPath path) {
      return create(visibility, path);
    }
    public bool is_Use { get { return true; } }
    public RAST._IVisibility dtor_visibility {
      get {
        return this._visibility;
      }
    }
    public RAST._IPath dtor_path {
      get {
        return this._path;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_visibility)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("use ")), ((this).dtor_path)._ToString()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
    }
  }

  public interface _ITopFnDecl {
    bool is_TopFn { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<RAST._IAttribute> dtor_attributes { get; }
    RAST._IVisibility dtor_visibility { get; }
    RAST._IFn dtor_fn { get; }
    _ITopFnDecl DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class TopFnDecl : _ITopFnDecl {
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<RAST._IAttribute> _attributes;
    public readonly RAST._IVisibility _visibility;
    public readonly RAST._IFn _fn;
    public TopFnDecl(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, RAST._IVisibility visibility, RAST._IFn fn) {
      this._docString = docString;
      this._attributes = attributes;
      this._visibility = visibility;
      this._fn = fn;
    }
    public _ITopFnDecl DowncastClone() {
      if (this is _ITopFnDecl dt) { return dt; }
      return new TopFnDecl(_docString, _attributes, _visibility, _fn);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.TopFnDecl;
      return oth != null && object.Equals(this._docString, oth._docString) && object.Equals(this._attributes, oth._attributes) && object.Equals(this._visibility, oth._visibility) && object.Equals(this._fn, oth._fn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._visibility));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.TopFnDecl.TopFn";
      s += "(";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._visibility);
      s += ", ";
      s += Dafny.Helpers.ToString(this._fn);
      s += ")";
      return s;
    }
    private static readonly RAST._ITopFnDecl theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IAttribute>.Empty, RAST.Visibility.Default(), RAST.Fn.Default());
    public static RAST._ITopFnDecl Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._ITopFnDecl> _TYPE = new Dafny.TypeDescriptor<RAST._ITopFnDecl>(RAST.TopFnDecl.Default());
    public static Dafny.TypeDescriptor<RAST._ITopFnDecl> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITopFnDecl create(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, RAST._IVisibility visibility, RAST._IFn fn) {
      return new TopFnDecl(docString, attributes, visibility, fn);
    }
    public static _ITopFnDecl create_TopFn(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, RAST._IVisibility visibility, RAST._IFn fn) {
      return create(docString, attributes, visibility, fn);
    }
    public bool is_TopFn { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<RAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
    public RAST._IVisibility dtor_visibility {
      get {
        return this._visibility;
      }
    }
    public RAST._IFn dtor_fn {
      get {
        return this._fn;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.ToDocstringPrefix((this).dtor_docString, ind), RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind)), ((this).dtor_visibility)._ToString()), ((this).dtor_fn)._ToString(ind));
    }
  }

  public interface _IAttribute {
    bool is_ApplyAttribute { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_derived { get; }
    _IAttribute DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Attribute : _IAttribute {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _derived;
    public Attribute(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> derived) {
      this._name = name;
      this._derived = derived;
    }
    public _IAttribute DowncastClone() {
      if (this is _IAttribute dt) { return dt; }
      return new Attribute(_name, _derived);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Attribute;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._derived, oth._derived);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._derived));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Attribute.ApplyAttribute";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._derived);
      s += ")";
      return s;
    }
    private static readonly RAST._IAttribute theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty);
    public static RAST._IAttribute Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IAttribute> _TYPE = new Dafny.TypeDescriptor<RAST._IAttribute>(RAST.Attribute.Default());
    public static Dafny.TypeDescriptor<RAST._IAttribute> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAttribute create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> derived) {
      return new Attribute(name, derived);
    }
    public static _IAttribute create_ApplyAttribute(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> derived) {
      return create(name, derived);
    }
    public bool is_ApplyAttribute { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_derived {
      get {
        return this._derived;
      }
    }
    public static RAST._IAttribute Name(Dafny.ISequence<Dafny.Rune> name) {
      return RAST.Attribute.create(name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      RAST._IAttribute _source0 = this;
      {
        Dafny.ISequence<Dafny.Rune> _0_name = _source0.dtor_name;
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1_derived = _source0.dtor_derived;
        Dafny.ISequence<Dafny.Rune> _2_arguments = (((new BigInteger((_1_derived).Count)).Sign != 0) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_1_derived, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_3_derived) => {
          return _3_derived;
        })), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#["), _0_name), _2_arguments), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
      }
    }
    public static Dafny.ISequence<Dafny.Rune> ToStringMultiple(Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> ind)
    {
      return RAST.__default.SeqToString<RAST._IAttribute>(attributes, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IAttribute, Dafny.ISequence<Dafny.Rune>>>>((_0_ind) => ((System.Func<RAST._IAttribute, Dafny.ISequence<Dafny.Rune>>)((_1_attribute) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1_attribute)._ToString(_0_ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), _0_ind);
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
    }
    public static RAST._IAttribute DeriveClone { get {
      return RAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("derive"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Clone")));
    } }
    public static RAST._IAttribute DeriveCloneAndCopy { get {
      return RAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("derive"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Clone"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Copy")));
    } }
    public static RAST._IAttribute CfgTest { get {
      return RAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cfg"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test")));
    } }
  }

  public interface _IStruct {
    bool is_Struct { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<RAST._IAttribute> dtor_attributes { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams { get; }
    RAST._IFields dtor_fields { get; }
    _IStruct DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Struct : _IStruct {
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<RAST._IAttribute> _attributes;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly RAST._IFields _fields;
    public Struct(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IFields fields) {
      this._docString = docString;
      this._attributes = attributes;
      this._name = name;
      this._typeParams = typeParams;
      this._fields = fields;
    }
    public _IStruct DowncastClone() {
      if (this is _IStruct dt) { return dt; }
      return new Struct(_docString, _attributes, _name, _typeParams, _fields);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Struct;
      return oth != null && object.Equals(this._docString, oth._docString) && object.Equals(this._attributes, oth._attributes) && object.Equals(this._name, oth._name) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._fields, oth._fields);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fields));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Struct.Struct";
      s += "(";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._fields);
      s += ")";
      return s;
    }
    private static readonly RAST._IStruct theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IAttribute>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._ITypeParamDecl>.Empty, RAST.Fields.Default());
    public static RAST._IStruct Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IStruct> _TYPE = new Dafny.TypeDescriptor<RAST._IStruct>(RAST.Struct.Default());
    public static Dafny.TypeDescriptor<RAST._IStruct> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStruct create(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IFields fields) {
      return new Struct(docString, attributes, name, typeParams, fields);
    }
    public static _IStruct create_Struct(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IFields fields) {
      return create(docString, attributes, name, typeParams, fields);
    }
    public bool is_Struct { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<RAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public RAST._IFields dtor_fields {
      get {
        return this._fields;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.ToDocstringPrefix((this).dtor_docString, ind), RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub struct ")), (this).dtor_name), RAST.TypeParamDecl.ToStringMultiple((this).dtor_typeParams, ind)), ((this).dtor_fields)._ToString(ind, ((this).dtor_fields).is_NamedFields)), ((((this).dtor_fields).is_NamelessFields) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))));
    }
  }

  public interface _ITypeSynonym {
    bool is_TypeSynonym { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<RAST._IAttribute> dtor_attributes { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams { get; }
    RAST._IType dtor_tpe { get; }
    _ITypeSynonym DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class TypeSynonym : _ITypeSynonym {
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<RAST._IAttribute> _attributes;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly RAST._IType _tpe;
    public TypeSynonym(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe) {
      this._docString = docString;
      this._attributes = attributes;
      this._name = name;
      this._typeParams = typeParams;
      this._tpe = tpe;
    }
    public _ITypeSynonym DowncastClone() {
      if (this is _ITypeSynonym dt) { return dt; }
      return new TypeSynonym(_docString, _attributes, _name, _typeParams, _tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.TypeSynonym;
      return oth != null && object.Equals(this._docString, oth._docString) && object.Equals(this._attributes, oth._attributes) && object.Equals(this._name, oth._name) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._tpe, oth._tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.TypeSynonym.TypeSynonym";
      s += "(";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ")";
      return s;
    }
    private static readonly RAST._ITypeSynonym theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IAttribute>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._ITypeParamDecl>.Empty, RAST.Type.Default());
    public static RAST._ITypeSynonym Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._ITypeSynonym> _TYPE = new Dafny.TypeDescriptor<RAST._ITypeSynonym>(RAST.TypeSynonym.Default());
    public static Dafny.TypeDescriptor<RAST._ITypeSynonym> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITypeSynonym create(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe) {
      return new TypeSynonym(docString, attributes, name, typeParams, tpe);
    }
    public static _ITypeSynonym create_TypeSynonym(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe) {
      return create(docString, attributes, name, typeParams, tpe);
    }
    public bool is_TypeSynonym { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<RAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        return this._tpe;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.ToDocstringPrefix((this).dtor_docString, ind), RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub type ")), (this).dtor_name), RAST.TypeParamDecl.ToStringMultiple((this).dtor_typeParams, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), ((this).dtor_tpe)._ToString(ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
    }
  }

  public interface _IConstant {
    bool is_Constant { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<RAST._IAttribute> dtor_attributes { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IType dtor_tpe { get; }
    RAST._IExpr dtor_value { get; }
    _IConstant DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Constant : _IConstant {
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<RAST._IAttribute> _attributes;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly RAST._IType _tpe;
    public readonly RAST._IExpr _value;
    public Constant(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe, RAST._IExpr @value) {
      this._docString = docString;
      this._attributes = attributes;
      this._name = name;
      this._tpe = tpe;
      this._value = @value;
    }
    public _IConstant DowncastClone() {
      if (this is _IConstant dt) { return dt; }
      return new Constant(_docString, _attributes, _name, _tpe, _value);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Constant;
      return oth != null && object.Equals(this._docString, oth._docString) && object.Equals(this._attributes, oth._attributes) && object.Equals(this._name, oth._name) && object.Equals(this._tpe, oth._tpe) && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Constant.Constant";
      s += "(";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ", ";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
    private static readonly RAST._IConstant theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IAttribute>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, RAST.Type.Default(), RAST.Expr.Default());
    public static RAST._IConstant Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IConstant> _TYPE = new Dafny.TypeDescriptor<RAST._IConstant>(RAST.Constant.Default());
    public static Dafny.TypeDescriptor<RAST._IConstant> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IConstant create(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe, RAST._IExpr @value) {
      return new Constant(docString, attributes, name, tpe, @value);
    }
    public static _IConstant create_Constant(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe, RAST._IExpr @value) {
      return create(docString, attributes, name, tpe, @value);
    }
    public bool is_Constant { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<RAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        return this._tpe;
      }
    }
    public RAST._IExpr dtor_value {
      get {
        return this._value;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.ToDocstringPrefix((this).dtor_docString, ind), RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub const ")), (this).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((this).dtor_tpe)._ToString(ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), ((this).dtor_value)._ToString(ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
    }
  }

  public interface _INamelessField {
    bool is_NamelessField { get; }
    RAST._IVisibility dtor_visibility { get; }
    RAST._IType dtor_tpe { get; }
    _INamelessField DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class NamelessField : _INamelessField {
    public readonly RAST._IVisibility _visibility;
    public readonly RAST._IType _tpe;
    public NamelessField(RAST._IVisibility visibility, RAST._IType tpe) {
      this._visibility = visibility;
      this._tpe = tpe;
    }
    public _INamelessField DowncastClone() {
      if (this is _INamelessField dt) { return dt; }
      return new NamelessField(_visibility, _tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.NamelessField;
      return oth != null && object.Equals(this._visibility, oth._visibility) && object.Equals(this._tpe, oth._tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._visibility));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.NamelessField.NamelessField";
      s += "(";
      s += Dafny.Helpers.ToString(this._visibility);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ")";
      return s;
    }
    private static readonly RAST._INamelessField theDefault = create(RAST.Visibility.Default(), RAST.Type.Default());
    public static RAST._INamelessField Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._INamelessField> _TYPE = new Dafny.TypeDescriptor<RAST._INamelessField>(RAST.NamelessField.Default());
    public static Dafny.TypeDescriptor<RAST._INamelessField> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INamelessField create(RAST._IVisibility visibility, RAST._IType tpe) {
      return new NamelessField(visibility, tpe);
    }
    public static _INamelessField create_NamelessField(RAST._IVisibility visibility, RAST._IType tpe) {
      return create(visibility, tpe);
    }
    public bool is_NamelessField { get { return true; } }
    public RAST._IVisibility dtor_visibility {
      get {
        return this._visibility;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        return this._tpe;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_visibility)._ToString(), ((this).dtor_tpe)._ToString(ind));
    }
  }

  public interface _IField {
    bool is_Field { get; }
    RAST._IVisibility dtor_visibility { get; }
    RAST._IFormal dtor_formal { get; }
    _IField DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
    RAST._INamelessField ToNamelessField();
  }
  public class Field : _IField {
    public readonly RAST._IVisibility _visibility;
    public readonly RAST._IFormal _formal;
    public Field(RAST._IVisibility visibility, RAST._IFormal formal) {
      this._visibility = visibility;
      this._formal = formal;
    }
    public _IField DowncastClone() {
      if (this is _IField dt) { return dt; }
      return new Field(_visibility, _formal);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Field;
      return oth != null && object.Equals(this._visibility, oth._visibility) && object.Equals(this._formal, oth._formal);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._visibility));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._formal));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Field.Field";
      s += "(";
      s += Dafny.Helpers.ToString(this._visibility);
      s += ", ";
      s += Dafny.Helpers.ToString(this._formal);
      s += ")";
      return s;
    }
    private static readonly RAST._IField theDefault = create(RAST.Visibility.Default(), RAST.Formal.Default());
    public static RAST._IField Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IField> _TYPE = new Dafny.TypeDescriptor<RAST._IField>(RAST.Field.Default());
    public static Dafny.TypeDescriptor<RAST._IField> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IField create(RAST._IVisibility visibility, RAST._IFormal formal) {
      return new Field(visibility, formal);
    }
    public static _IField create_Field(RAST._IVisibility visibility, RAST._IFormal formal) {
      return create(visibility, formal);
    }
    public bool is_Field { get { return true; } }
    public RAST._IVisibility dtor_visibility {
      get {
        return this._visibility;
      }
    }
    public RAST._IFormal dtor_formal {
      get {
        return this._formal;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_visibility)._ToString(), ((this).dtor_formal)._ToString(ind));
    }
    public RAST._INamelessField ToNamelessField() {
      return RAST.NamelessField.create((this).dtor_visibility, ((this).dtor_formal).dtor_tpe);
    }
  }

  public interface _IFields {
    bool is_NamedFields { get; }
    bool is_NamelessFields { get; }
    Dafny.ISequence<RAST._IField> dtor_fields { get; }
    Dafny.ISequence<RAST._INamelessField> dtor_types { get; }
    _IFields DowncastClone();
    RAST._IFields ToNamelessFields();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind, bool newLine);
  }
  public abstract class Fields : _IFields {
    public Fields() {
    }
    private static readonly RAST._IFields theDefault = create_NamedFields(Dafny.Sequence<RAST._IField>.Empty);
    public static RAST._IFields Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IFields> _TYPE = new Dafny.TypeDescriptor<RAST._IFields>(RAST.Fields.Default());
    public static Dafny.TypeDescriptor<RAST._IFields> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IFields create_NamedFields(Dafny.ISequence<RAST._IField> fields) {
      return new Fields_NamedFields(fields);
    }
    public static _IFields create_NamelessFields(Dafny.ISequence<RAST._INamelessField> types) {
      return new Fields_NamelessFields(types);
    }
    public bool is_NamedFields { get { return this is Fields_NamedFields; } }
    public bool is_NamelessFields { get { return this is Fields_NamelessFields; } }
    public Dafny.ISequence<RAST._IField> dtor_fields {
      get {
        var d = this;
        return ((Fields_NamedFields)d)._fields;
      }
    }
    public Dafny.ISequence<RAST._INamelessField> dtor_types {
      get {
        var d = this;
        return ((Fields_NamelessFields)d)._types;
      }
    }
    public abstract _IFields DowncastClone();
    public RAST._IFields ToNamelessFields() {
      return RAST.Fields.create_NamelessFields(((System.Func<Dafny.ISequence<RAST._INamelessField>>) (() => {
  BigInteger dim15 = new BigInteger(((this).dtor_fields).Count);
  var arr15 = new RAST._INamelessField[Dafny.Helpers.ToIntChecked(dim15, "array size exceeds memory limit")];
  for (int i15 = 0; i15 < dim15; i15++) {
    var _0_i = (BigInteger) i15;
    arr15[(int)(_0_i)] = (((this).dtor_fields).Select(_0_i)).ToNamelessField();
  }
  return Dafny.Sequence<RAST._INamelessField>.FromArray(arr15);
}))());
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind, bool newLine)
    {
      if ((this).is_NamedFields) {
        Dafny.ISequence<Dafny.Rune> _0_separator = ((newLine) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"), ind), RAST.__default.IND)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")));
        _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs0 = (((newLine) && ((new BigInteger(((this).dtor_fields).Count)).Sign == 1)) ? (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind))) : ((((new BigInteger(((this).dtor_fields).Count)).Sign == 1) ? (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "))) : (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
        Dafny.ISequence<Dafny.Rune> _1_beginSpace = _let_tmp_rhs0.dtor__0;
        Dafny.ISequence<Dafny.Rune> _2_endSpace = _let_tmp_rhs0.dtor__1;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {"), _1_beginSpace), RAST.__default.SeqToString<RAST._IField>((this).dtor_fields, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IField, Dafny.ISequence<Dafny.Rune>>>>((_3_ind) => ((System.Func<RAST._IField, Dafny.ISequence<Dafny.Rune>>)((_4_field) => {
          return (_4_field)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_3_ind, RAST.__default.IND));
        })))(ind), _0_separator)), _2_endSpace), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
      } else {
        Dafny.ISequence<Dafny.Rune> _5_separator = ((newLine) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"), ind), RAST.__default.IND)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", ")));
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<RAST._INamelessField>((this).dtor_types, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._INamelessField, Dafny.ISequence<Dafny.Rune>>>>((_6_ind) => ((System.Func<RAST._INamelessField, Dafny.ISequence<Dafny.Rune>>)((_7_t) => {
          return (_7_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_6_ind, RAST.__default.IND));
        })))(ind), _5_separator)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      }
    }
  }
  public class Fields_NamedFields : Fields {
    public readonly Dafny.ISequence<RAST._IField> _fields;
    public Fields_NamedFields(Dafny.ISequence<RAST._IField> fields) : base() {
      this._fields = fields;
    }
    public override _IFields DowncastClone() {
      if (this is _IFields dt) { return dt; }
      return new Fields_NamedFields(_fields);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Fields_NamedFields;
      return oth != null && object.Equals(this._fields, oth._fields);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fields));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Fields.NamedFields";
      s += "(";
      s += Dafny.Helpers.ToString(this._fields);
      s += ")";
      return s;
    }
  }
  public class Fields_NamelessFields : Fields {
    public readonly Dafny.ISequence<RAST._INamelessField> _types;
    public Fields_NamelessFields(Dafny.ISequence<RAST._INamelessField> types) : base() {
      this._types = types;
    }
    public override _IFields DowncastClone() {
      if (this is _IFields dt) { return dt; }
      return new Fields_NamelessFields(_types);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Fields_NamelessFields;
      return oth != null && object.Equals(this._types, oth._types);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._types));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Fields.NamelessFields";
      s += "(";
      s += Dafny.Helpers.ToString(this._types);
      s += ")";
      return s;
    }
  }

  public interface _IEnumCase {
    bool is_EnumCase { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IFields dtor_fields { get; }
    _IEnumCase DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind, bool newLine);
  }
  public class EnumCase : _IEnumCase {
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly RAST._IFields _fields;
    public EnumCase(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<Dafny.Rune> name, RAST._IFields fields) {
      this._docString = docString;
      this._name = name;
      this._fields = fields;
    }
    public _IEnumCase DowncastClone() {
      if (this is _IEnumCase dt) { return dt; }
      return new EnumCase(_docString, _name, _fields);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.EnumCase;
      return oth != null && object.Equals(this._docString, oth._docString) && object.Equals(this._name, oth._name) && object.Equals(this._fields, oth._fields);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fields));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.EnumCase.EnumCase";
      s += "(";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._fields);
      s += ")";
      return s;
    }
    private static readonly RAST._IEnumCase theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, RAST.Fields.Default());
    public static RAST._IEnumCase Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IEnumCase> _TYPE = new Dafny.TypeDescriptor<RAST._IEnumCase>(RAST.EnumCase.Default());
    public static Dafny.TypeDescriptor<RAST._IEnumCase> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnumCase create(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<Dafny.Rune> name, RAST._IFields fields) {
      return new EnumCase(docString, name, fields);
    }
    public static _IEnumCase create_EnumCase(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<Dafny.Rune> name, RAST._IFields fields) {
      return create(docString, name, fields);
    }
    public bool is_EnumCase { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public RAST._IFields dtor_fields {
      get {
        return this._fields;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind, bool newLine)
    {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.ToDocstringPrefix((this).dtor_docString, ind), (this).dtor_name), ((this).dtor_fields)._ToString(ind, newLine));
    }
  }

  public interface _IEnum {
    bool is_Enum { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<RAST._IAttribute> dtor_attributes { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams { get; }
    Dafny.ISequence<RAST._IEnumCase> dtor_variants { get; }
    _IEnum DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Enum : _IEnum {
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<RAST._IAttribute> _attributes;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly Dafny.ISequence<RAST._IEnumCase> _variants;
    public Enum(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IEnumCase> variants) {
      this._docString = docString;
      this._attributes = attributes;
      this._name = name;
      this._typeParams = typeParams;
      this._variants = variants;
    }
    public _IEnum DowncastClone() {
      if (this is _IEnum dt) { return dt; }
      return new Enum(_docString, _attributes, _name, _typeParams, _variants);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Enum;
      return oth != null && object.Equals(this._docString, oth._docString) && object.Equals(this._attributes, oth._attributes) && object.Equals(this._name, oth._name) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._variants, oth._variants);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._variants));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Enum.Enum";
      s += "(";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._variants);
      s += ")";
      return s;
    }
    private static readonly RAST._IEnum theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IAttribute>.Empty, Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._ITypeParamDecl>.Empty, Dafny.Sequence<RAST._IEnumCase>.Empty);
    public static RAST._IEnum Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IEnum> _TYPE = new Dafny.TypeDescriptor<RAST._IEnum>(RAST.Enum.Default());
    public static Dafny.TypeDescriptor<RAST._IEnum> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnum create(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IEnumCase> variants) {
      return new Enum(docString, attributes, name, typeParams, variants);
    }
    public static _IEnum create_Enum(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IEnumCase> variants) {
      return create(docString, attributes, name, typeParams, variants);
    }
    public bool is_Enum { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<RAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public Dafny.ISequence<RAST._IEnumCase> dtor_variants {
      get {
        return this._variants;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.ToDocstringPrefix((this).dtor_docString, ind), RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub enum ")), (this).dtor_name), RAST.TypeParamDecl.ToStringMultiple((this).dtor_typeParams, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IEnumCase>((this).dtor_variants, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IEnumCase, Dafny.ISequence<Dafny.Rune>>>>((_0_ind) => ((System.Func<RAST._IEnumCase, Dafny.ISequence<Dafny.Rune>>)((_1_variant) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _0_ind), RAST.__default.IND), (_1_variant)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_0_ind, RAST.__default.IND), true));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
    }
  }

  public interface _ITypeParamDecl {
    bool is_TypeParamDecl { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<RAST._IType> dtor_constraints { get; }
    _ITypeParamDecl DowncastClone();
    RAST._ITypeParamDecl AddConstraints(Dafny.ISequence<RAST._IType> constraints);
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class TypeParamDecl : _ITypeParamDecl {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._IType> _constraints;
    public TypeParamDecl(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._IType> constraints) {
      this._name = name;
      this._constraints = constraints;
    }
    public _ITypeParamDecl DowncastClone() {
      if (this is _ITypeParamDecl dt) { return dt; }
      return new TypeParamDecl(_name, _constraints);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.TypeParamDecl;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._constraints, oth._constraints);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._constraints));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.TypeParamDecl.TypeParamDecl";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._constraints);
      s += ")";
      return s;
    }
    private static readonly RAST._ITypeParamDecl theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IType>.Empty);
    public static RAST._ITypeParamDecl Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._ITypeParamDecl> _TYPE = new Dafny.TypeDescriptor<RAST._ITypeParamDecl>(RAST.TypeParamDecl.Default());
    public static Dafny.TypeDescriptor<RAST._ITypeParamDecl> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITypeParamDecl create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._IType> constraints) {
      return new TypeParamDecl(name, constraints);
    }
    public static _ITypeParamDecl create_TypeParamDecl(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._IType> constraints) {
      return create(name, constraints);
    }
    public bool is_TypeParamDecl { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<RAST._IType> dtor_constraints {
      get {
        return this._constraints;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> ToStringMultiple(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<Dafny.Rune> ind)
    {
      if ((new BigInteger((typeParams).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), RAST.__default.SeqToString<RAST._ITypeParamDecl>(typeParams, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._ITypeParamDecl, Dafny.ISequence<Dafny.Rune>>>>((_0_ind) => ((System.Func<RAST._ITypeParamDecl, Dafny.ISequence<Dafny.Rune>>)((_1_t) => {
          return (_1_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_0_ind, RAST.__default.IND));
        })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
      }
    }
    public static Dafny.ISequence<RAST._ITypeParamDecl> AddConstraintsMultiple(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IType> constraints)
    {
      Dafny.ISequence<RAST._ITypeParamDecl> _0___accumulator = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((typeParams).Count)).Sign == 0) {
        return Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_0___accumulator, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements());
      } else {
        _0___accumulator = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_0___accumulator, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(((typeParams).Select(BigInteger.Zero)).AddConstraints(constraints)));
        Dafny.ISequence<RAST._ITypeParamDecl> _in0 = (typeParams).Drop(BigInteger.One);
        Dafny.ISequence<RAST._IType> _in1 = constraints;
        typeParams = _in0;
        constraints = _in1;
        goto TAIL_CALL_START;
      }
    }
    public RAST._ITypeParamDecl AddConstraints(Dafny.ISequence<RAST._IType> constraints) {
      RAST._ITypeParamDecl _0_dt__update__tmp_h0 = this;
      Dafny.ISequence<RAST._IType> _1_dt__update_hconstraints_h0 = Dafny.Sequence<RAST._IType>.Concat((this).dtor_constraints, constraints);
      return RAST.TypeParamDecl.create((_0_dt__update__tmp_h0).dtor_name, _1_dt__update_hconstraints_h0);
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_name, (((new BigInteger(((this).dtor_constraints).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": "), RAST.__default.SeqToString<RAST._IType>((this).dtor_constraints, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_0_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_1_t) => {
        return (_1_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_0_ind, RAST.__default.IND));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + "))))));
    }
  }

  public interface _IPath {
    bool is_Global { get; }
    bool is_Crate { get; }
    bool is_Self { get; }
    bool is_PMemberSelect { get; }
    RAST._IPath dtor_base { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    _IPath DowncastClone();
    RAST._IPath ToDowncast();
    RAST._IPath MSel(Dafny.ISequence<Dafny.Rune> name);
    RAST._IPath MSels(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names);
    RAST._IExpr FSel(Dafny.ISequence<Dafny.Rune> name);
    RAST._IType AsType();
    RAST._IExpr AsExpr();
    Dafny.ISequence<Dafny.Rune> _ToString();
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> RightMostIdentifier();
  }
  public abstract class Path : _IPath {
    public Path() {
    }
    private static readonly RAST._IPath theDefault = create_Global();
    public static RAST._IPath Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IPath> _TYPE = new Dafny.TypeDescriptor<RAST._IPath>(RAST.Path.Default());
    public static Dafny.TypeDescriptor<RAST._IPath> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPath create_Global() {
      return new Path_Global();
    }
    public static _IPath create_Crate() {
      return new Path_Crate();
    }
    public static _IPath create_Self() {
      return new Path_Self();
    }
    public static _IPath create_PMemberSelect(RAST._IPath @base, Dafny.ISequence<Dafny.Rune> name) {
      return new Path_PMemberSelect(@base, name);
    }
    public bool is_Global { get { return this is Path_Global; } }
    public bool is_Crate { get { return this is Path_Crate; } }
    public bool is_Self { get { return this is Path_Self; } }
    public bool is_PMemberSelect { get { return this is Path_PMemberSelect; } }
    public RAST._IPath dtor_base {
      get {
        var d = this;
        return ((Path_PMemberSelect)d)._base;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        return ((Path_PMemberSelect)d)._name;
      }
    }
    public abstract _IPath DowncastClone();
    public RAST._IPath ToDowncast() {
      RAST._IPath _source0 = this;
      {
        if (_source0.is_PMemberSelect) {
          RAST._IPath _0_base = _source0.dtor_base;
          Dafny.ISequence<Dafny.Rune> _1_name = _source0.dtor_name;
          return RAST.Path.create_PMemberSelect(_0_base, Dafny.Sequence<Dafny.Rune>.Concat(RAST.Path.DowncastPrefix, _1_name));
        }
      }
      {
        return this;
      }
    }
    public RAST._IPath MSel(Dafny.ISequence<Dafny.Rune> name) {
      return RAST.Path.create_PMemberSelect(this, name);
    }
    public RAST._IPath MSels(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names) {
      _IPath _this = this;
    TAIL_CALL_START: ;
      if ((new BigInteger((names).Count)).Sign == 0) {
        return _this;
      } else {
        RAST._IPath _in0 = (_this).MSel((names).Select(BigInteger.Zero));
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _in1 = (names).Drop(BigInteger.One);
        _this = _in0;
        ;
        names = _in1;
        goto TAIL_CALL_START;
      }
    }
    public RAST._IExpr FSel(Dafny.ISequence<Dafny.Rune> name) {
      return ((this).AsExpr()).FSel(name);
    }
    public RAST._IType AsType() {
      return RAST.Type.create_TypeFromPath(this);
    }
    public RAST._IExpr AsExpr() {
      return RAST.Expr.create_ExprFromPath(this);
    }
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      RAST._IPath _source0 = this;
      {
        if (_source0.is_Global) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
      }
      {
        if (_source0.is_Crate) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate");
        }
      }
      {
        if (_source0.is_Self) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self");
        }
      }
      {
        RAST._IPath _0_base = _source0.dtor_base;
        Dafny.ISequence<Dafny.Rune> _1_name = _source0.dtor_name;
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_0_base)._ToString(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1_name);
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> RightMostIdentifier() {
      RAST._IPath _source0 = this;
      {
        if (_source0.is_Global) {
          return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
        }
      }
      {
        if (_source0.is_Crate) {
          return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"));
        }
      }
      {
        if (_source0.is_Self) {
          return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self"));
        }
      }
      {
        RAST._IPath _0_base = _source0.dtor_base;
        Dafny.ISequence<Dafny.Rune> _1_name = _source0.dtor_name;
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1_name);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> DowncastPrefix { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_Downcast_");
    } }
  }
  public class Path_Global : Path {
    public Path_Global() : base() {
    }
    public override _IPath DowncastClone() {
      if (this is _IPath dt) { return dt; }
      return new Path_Global();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Path_Global;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Path.Global";
      return s;
    }
  }
  public class Path_Crate : Path {
    public Path_Crate() : base() {
    }
    public override _IPath DowncastClone() {
      if (this is _IPath dt) { return dt; }
      return new Path_Crate();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Path_Crate;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Path.Crate";
      return s;
    }
  }
  public class Path_Self : Path {
    public Path_Self() : base() {
    }
    public override _IPath DowncastClone() {
      if (this is _IPath dt) { return dt; }
      return new Path_Self();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Path_Self;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Path.Self";
      return s;
    }
  }
  public class Path_PMemberSelect : Path {
    public readonly RAST._IPath _base;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public Path_PMemberSelect(RAST._IPath @base, Dafny.ISequence<Dafny.Rune> name) : base() {
      this._base = @base;
      this._name = name;
    }
    public override _IPath DowncastClone() {
      if (this is _IPath dt) { return dt; }
      return new Path_PMemberSelect(_base, _name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Path_PMemberSelect;
      return oth != null && object.Equals(this._base, oth._base) && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._base));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Path.PMemberSelect";
      s += "(";
      s += Dafny.Helpers.ToString(this._base);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }

  public interface _IType {
    bool is_U8 { get; }
    bool is_U16 { get; }
    bool is_U32 { get; }
    bool is_U64 { get; }
    bool is_U128 { get; }
    bool is_I8 { get; }
    bool is_I16 { get; }
    bool is_I32 { get; }
    bool is_I64 { get; }
    bool is_I128 { get; }
    bool is_USIZE { get; }
    bool is_Bool { get; }
    bool is_TIdentifier { get; }
    bool is_TypeFromPath { get; }
    bool is_TypeApp { get; }
    bool is_Borrowed { get; }
    bool is_BorrowedMut { get; }
    bool is_ImplType { get; }
    bool is_DynType { get; }
    bool is_TupleType { get; }
    bool is_FnType { get; }
    bool is_IntersectionType { get; }
    bool is_Array { get; }
    bool is_TSynonym { get; }
    bool is_TMetaData { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IPath dtor_path { get; }
    RAST._IType dtor_baseName { get; }
    Dafny.ISequence<RAST._IType> dtor_arguments { get; }
    RAST._IType dtor_underlying { get; }
    RAST._IType dtor_returnType { get; }
    RAST._IType dtor_left { get; }
    RAST._IType dtor_right { get; }
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_size { get; }
    RAST._IType dtor_display { get; }
    RAST._IType dtor_base { get; }
    bool dtor_copySemantics { get; }
    bool dtor_overflow { get; }
    _IType DowncastClone();
    RAST._IType RemoveSynonyms();
    Std.Wrappers._IOption<RAST._IType> ToDowncast();
    Std.Wrappers._IOption<RAST._IExpr> ToDowncastExpr();
    Std.Wrappers._IOption<RAST._IExpr> ToExpr();
    RAST._IType Expand();
    bool EndsWithNameThatCanAcceptGenerics();
    RAST._IType ReplaceMap(Dafny.IMap<RAST._IType,RAST._IType> mapping);
    RAST._IType Replace(Func<RAST._IType, RAST._IType> mapping);
    __T Fold<__T>(__T acc, Func<__T, RAST._IType, __T> f);
    bool IsAutoSize();
    bool CanReadWithoutClone();
    bool IsRcOrBorrowedRc();
    Std.Wrappers._IOption<RAST._IType> ExtractMaybePlacebo();
    Std.Wrappers._IOption<RAST._IType> ExtractMaybeUninitArrayElement();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
    RAST._IType Apply1(RAST._IType arg);
    RAST._IType Apply(Dafny.ISequence<RAST._IType> args);
    RAST._IType ToOwned();
    RAST._IExpr ToNullExpr();
    bool IsMultiArray();
    Dafny.ISequence<Dafny.Rune> MultiArrayClass();
    RAST._IType MultiArrayUnderlying();
    RAST._IType TypeAtInitialization();
    bool IsMaybeUninit();
    bool IsUninitArray();
    bool IsBox();
    bool NeedsAsRefForBorrow();
    RAST._IType BoxUnderlying();
    bool IsObject();
    bool IsPointer();
    bool IsObjectOrPointer();
    RAST._IType ObjectOrPointerUnderlying();
    bool IsBuiltinCollection();
    RAST._IType GetBuiltinCollectionElement();
    bool IsRc();
    RAST._IType RcUnderlying();
    bool IsBoxDyn();
    RAST._IType BoxDynUnderlying();
  }
  public abstract class Type : _IType {
    public Type() {
    }
    private static readonly RAST._IType theDefault = create_U8();
    public static RAST._IType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IType> _TYPE = new Dafny.TypeDescriptor<RAST._IType>(RAST.Type.Default());
    public static Dafny.TypeDescriptor<RAST._IType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IType create_U8() {
      return new Type_U8();
    }
    public static _IType create_U16() {
      return new Type_U16();
    }
    public static _IType create_U32() {
      return new Type_U32();
    }
    public static _IType create_U64() {
      return new Type_U64();
    }
    public static _IType create_U128() {
      return new Type_U128();
    }
    public static _IType create_I8() {
      return new Type_I8();
    }
    public static _IType create_I16() {
      return new Type_I16();
    }
    public static _IType create_I32() {
      return new Type_I32();
    }
    public static _IType create_I64() {
      return new Type_I64();
    }
    public static _IType create_I128() {
      return new Type_I128();
    }
    public static _IType create_USIZE() {
      return new Type_USIZE();
    }
    public static _IType create_Bool() {
      return new Type_Bool();
    }
    public static _IType create_TIdentifier(Dafny.ISequence<Dafny.Rune> name) {
      return new Type_TIdentifier(name);
    }
    public static _IType create_TypeFromPath(RAST._IPath path) {
      return new Type_TypeFromPath(path);
    }
    public static _IType create_TypeApp(RAST._IType baseName, Dafny.ISequence<RAST._IType> arguments) {
      return new Type_TypeApp(baseName, arguments);
    }
    public static _IType create_Borrowed(RAST._IType underlying) {
      return new Type_Borrowed(underlying);
    }
    public static _IType create_BorrowedMut(RAST._IType underlying) {
      return new Type_BorrowedMut(underlying);
    }
    public static _IType create_ImplType(RAST._IType underlying) {
      return new Type_ImplType(underlying);
    }
    public static _IType create_DynType(RAST._IType underlying) {
      return new Type_DynType(underlying);
    }
    public static _IType create_TupleType(Dafny.ISequence<RAST._IType> arguments) {
      return new Type_TupleType(arguments);
    }
    public static _IType create_FnType(Dafny.ISequence<RAST._IType> arguments, RAST._IType returnType) {
      return new Type_FnType(arguments, returnType);
    }
    public static _IType create_IntersectionType(RAST._IType left, RAST._IType right) {
      return new Type_IntersectionType(left, right);
    }
    public static _IType create_Array(RAST._IType underlying, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> size) {
      return new Type_Array(underlying, size);
    }
    public static _IType create_TSynonym(RAST._IType display, RAST._IType @base) {
      return new Type_TSynonym(display, @base);
    }
    public static _IType create_TMetaData(RAST._IType display, bool copySemantics, bool overflow) {
      return new Type_TMetaData(display, copySemantics, overflow);
    }
    public bool is_U8 { get { return this is Type_U8; } }
    public bool is_U16 { get { return this is Type_U16; } }
    public bool is_U32 { get { return this is Type_U32; } }
    public bool is_U64 { get { return this is Type_U64; } }
    public bool is_U128 { get { return this is Type_U128; } }
    public bool is_I8 { get { return this is Type_I8; } }
    public bool is_I16 { get { return this is Type_I16; } }
    public bool is_I32 { get { return this is Type_I32; } }
    public bool is_I64 { get { return this is Type_I64; } }
    public bool is_I128 { get { return this is Type_I128; } }
    public bool is_USIZE { get { return this is Type_USIZE; } }
    public bool is_Bool { get { return this is Type_Bool; } }
    public bool is_TIdentifier { get { return this is Type_TIdentifier; } }
    public bool is_TypeFromPath { get { return this is Type_TypeFromPath; } }
    public bool is_TypeApp { get { return this is Type_TypeApp; } }
    public bool is_Borrowed { get { return this is Type_Borrowed; } }
    public bool is_BorrowedMut { get { return this is Type_BorrowedMut; } }
    public bool is_ImplType { get { return this is Type_ImplType; } }
    public bool is_DynType { get { return this is Type_DynType; } }
    public bool is_TupleType { get { return this is Type_TupleType; } }
    public bool is_FnType { get { return this is Type_FnType; } }
    public bool is_IntersectionType { get { return this is Type_IntersectionType; } }
    public bool is_Array { get { return this is Type_Array; } }
    public bool is_TSynonym { get { return this is Type_TSynonym; } }
    public bool is_TMetaData { get { return this is Type_TMetaData; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        return ((Type_TIdentifier)d)._name;
      }
    }
    public RAST._IPath dtor_path {
      get {
        var d = this;
        return ((Type_TypeFromPath)d)._path;
      }
    }
    public RAST._IType dtor_baseName {
      get {
        var d = this;
        return ((Type_TypeApp)d)._baseName;
      }
    }
    public Dafny.ISequence<RAST._IType> dtor_arguments {
      get {
        var d = this;
        if (d is Type_TypeApp) { return ((Type_TypeApp)d)._arguments; }
        if (d is Type_TupleType) { return ((Type_TupleType)d)._arguments; }
        return ((Type_FnType)d)._arguments;
      }
    }
    public RAST._IType dtor_underlying {
      get {
        var d = this;
        if (d is Type_Borrowed) { return ((Type_Borrowed)d)._underlying; }
        if (d is Type_BorrowedMut) { return ((Type_BorrowedMut)d)._underlying; }
        if (d is Type_ImplType) { return ((Type_ImplType)d)._underlying; }
        if (d is Type_DynType) { return ((Type_DynType)d)._underlying; }
        return ((Type_Array)d)._underlying;
      }
    }
    public RAST._IType dtor_returnType {
      get {
        var d = this;
        return ((Type_FnType)d)._returnType;
      }
    }
    public RAST._IType dtor_left {
      get {
        var d = this;
        return ((Type_IntersectionType)d)._left;
      }
    }
    public RAST._IType dtor_right {
      get {
        var d = this;
        return ((Type_IntersectionType)d)._right;
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_size {
      get {
        var d = this;
        return ((Type_Array)d)._size;
      }
    }
    public RAST._IType dtor_display {
      get {
        var d = this;
        if (d is Type_TSynonym) { return ((Type_TSynonym)d)._display; }
        return ((Type_TMetaData)d)._display;
      }
    }
    public RAST._IType dtor_base {
      get {
        var d = this;
        return ((Type_TSynonym)d)._base;
      }
    }
    public bool dtor_copySemantics {
      get {
        var d = this;
        return ((Type_TMetaData)d)._copySemantics;
      }
    }
    public bool dtor_overflow {
      get {
        var d = this;
        return ((Type_TMetaData)d)._overflow;
      }
    }
    public abstract _IType DowncastClone();
    public RAST._IType RemoveSynonyms() {
      _IType _this = this;
    TAIL_CALL_START: ;
      RAST._IType _source0 = _this;
      {
        if (_source0.is_TSynonym) {
          RAST._IType _0_display = _source0.dtor_display;
          RAST._IType _1_base = _source0.dtor_base;
          RAST._IType _in0 = _0_display;
          _this = _in0;
          ;
          goto TAIL_CALL_START;
        }
      }
      {
        if (_source0.is_TMetaData) {
          RAST._IType _2_display = _source0.dtor_display;
          RAST._IType _in1 = _2_display;
          _this = _in1;
          ;
          goto TAIL_CALL_START;
        }
      }
      {
        return _this;
      }
    }
    public Std.Wrappers._IOption<RAST._IType> ToDowncast() {
      RAST._IType _0_t = (this).RemoveSynonyms();
      if ((_0_t).IsRc()) {
        return ((_0_t).RcUnderlying()).ToDowncast();
      } else if ((_0_t).IsBoxDyn()) {
        return ((_0_t).BoxDynUnderlying()).ToDowncast();
      } else {
        RAST._IType _source0 = _0_t;
        {
          if (_source0.is_TypeFromPath) {
            RAST._IPath _1_path = _source0.dtor_path;
            return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeFromPath((_1_path).ToDowncast()));
          }
        }
        {
          if (_source0.is_TypeApp) {
            RAST._IType _2_baseName = _source0.dtor_baseName;
            Dafny.ISequence<RAST._IType> _3_arguments = _source0.dtor_arguments;
            Std.Wrappers._IOption<RAST._IType> _4_valueOrError0 = (_2_baseName).ToDowncast();
            if ((_4_valueOrError0).IsFailure()) {
              return (_4_valueOrError0).PropagateFailure<RAST._IType>();
            } else {
              RAST._IType _5_baseNameExpr = (_4_valueOrError0).Extract();
              return Std.Wrappers.Option<RAST._IType>.create_Some((_5_baseNameExpr).Apply(_3_arguments));
            }
          }
        }
        {
          if (_source0.is_TIdentifier) {
            Dafny.ISequence<Dafny.Rune> _6_name = _source0.dtor_name;
            return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.Concat(RAST.Path.DowncastPrefix, _6_name)));
          }
        }
        {
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> ToDowncastExpr() {
      Std.Wrappers._IOption<RAST._IType> _0_valueOrError0 = (this).ToDowncast();
      if ((_0_valueOrError0).IsFailure()) {
        return (_0_valueOrError0).PropagateFailure<RAST._IExpr>();
      } else {
        RAST._IType _1_tpe = (_0_valueOrError0).Extract();
        return (_1_tpe).ToExpr();
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> ToExpr() {
      RAST._IType _source0 = this;
      {
        if (_source0.is_TypeFromPath) {
          RAST._IPath _0_path = _source0.dtor_path;
          return Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_ExprFromPath(_0_path));
        }
      }
      {
        if (_source0.is_TypeApp) {
          RAST._IType _1_baseName = _source0.dtor_baseName;
          Dafny.ISequence<RAST._IType> _2_arguments = _source0.dtor_arguments;
          Std.Wrappers._IOption<RAST._IExpr> _3_valueOrError0 = (_1_baseName).ToExpr();
          if ((_3_valueOrError0).IsFailure()) {
            return (_3_valueOrError0).PropagateFailure<RAST._IExpr>();
          } else {
            RAST._IExpr _4_baseNameExpr = (_3_valueOrError0).Extract();
            return Std.Wrappers.Option<RAST._IExpr>.create_Some((_4_baseNameExpr).ApplyType(_2_arguments));
          }
        }
      }
      {
        if (_source0.is_TSynonym) {
          RAST._IType _5_display = _source0.dtor_display;
          RAST._IType _6_base = _source0.dtor_base;
          return (_5_display).ToExpr();
        }
      }
      {
        if (_source0.is_TMetaData) {
          RAST._IType _7_display = _source0.dtor_display;
          return (_7_display).ToExpr();
        }
      }
      {
        if (_source0.is_TIdentifier) {
          Dafny.ISequence<Dafny.Rune> _8_name = _source0.dtor_name;
          return Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Identifier(_8_name));
        }
      }
      {
        return Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
    }
    public RAST._IType Expand() {
      _IType _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_TSynonym) {
        RAST._IType _in0 = (_this).dtor_base;
        _this = _in0;
        ;
        goto TAIL_CALL_START;
      } else if ((_this).is_TMetaData) {
        RAST._IType _in1 = (_this).dtor_display;
        _this = _in1;
        ;
        goto TAIL_CALL_START;
      } else {
        return _this;
      }
    }
    public bool EndsWithNameThatCanAcceptGenerics() {
      return ((((((((((((((((((this).is_U8) || ((this).is_U16)) || ((this).is_U32)) || ((this).is_U64)) || ((this).is_U128)) || ((this).is_I8)) || ((this).is_I16)) || ((this).is_I32)) || ((this).is_I64)) || ((this).is_I128)) || ((this).is_TIdentifier)) || ((this).is_TypeFromPath)) || (((this).is_Borrowed) && (((this).dtor_underlying).EndsWithNameThatCanAcceptGenerics()))) || (((this).is_BorrowedMut) && (((this).dtor_underlying).EndsWithNameThatCanAcceptGenerics()))) || (((this).is_ImplType) && (((this).dtor_underlying).EndsWithNameThatCanAcceptGenerics()))) || (((this).is_DynType) && (((this).dtor_underlying).EndsWithNameThatCanAcceptGenerics()))) || (((this).is_IntersectionType) && (((this).dtor_right).EndsWithNameThatCanAcceptGenerics()))) || ((((this).is_TSynonym) || ((this).is_TMetaData)) && (((this).dtor_display).EndsWithNameThatCanAcceptGenerics()));
    }
    public RAST._IType ReplaceMap(Dafny.IMap<RAST._IType,RAST._IType> mapping) {
      return (this).Replace(Dafny.Helpers.Id<Func<Dafny.IMap<RAST._IType,RAST._IType>, Func<RAST._IType, RAST._IType>>>((_0_mapping) => ((System.Func<RAST._IType, RAST._IType>)((_1_t) => {
        return (((_0_mapping).Contains(_1_t)) ? (Dafny.Map<RAST._IType, RAST._IType>.Select(_0_mapping,_1_t)) : (_1_t));
      })))(mapping));
    }
    public RAST._IType Replace(Func<RAST._IType, RAST._IType> mapping) {
      RAST._IType _0_r = ((System.Func<RAST._IType>)(() => {
        RAST._IType _source0 = this;
        {
          bool disjunctiveMatch0 = false;
          if (_source0.is_U8) {
            disjunctiveMatch0 = true;
          }
          if (_source0.is_U16) {
            disjunctiveMatch0 = true;
          }
          if (_source0.is_U32) {
            disjunctiveMatch0 = true;
          }
          if (_source0.is_U64) {
            disjunctiveMatch0 = true;
          }
          if (_source0.is_U128) {
            disjunctiveMatch0 = true;
          }
          if (_source0.is_I8) {
            disjunctiveMatch0 = true;
          }
          if (_source0.is_I16) {
            disjunctiveMatch0 = true;
          }
          if (_source0.is_I32) {
            disjunctiveMatch0 = true;
          }
          if (_source0.is_I64) {
            disjunctiveMatch0 = true;
          }
          if (_source0.is_I128) {
            disjunctiveMatch0 = true;
          }
          if (_source0.is_USIZE) {
            disjunctiveMatch0 = true;
          }
          if (_source0.is_Bool) {
            disjunctiveMatch0 = true;
          }
          if (disjunctiveMatch0) {
            return this;
          }
        }
        {
          if (_source0.is_TIdentifier) {
            return this;
          }
        }
        {
          if (_source0.is_TypeFromPath) {
            RAST._IPath _1_path = _source0.dtor_path;
            return this;
          }
        }
        {
          if (_source0.is_TypeApp) {
            RAST._IType _2_baseName = _source0.dtor_baseName;
            Dafny.ISequence<RAST._IType> _3_arguments = _source0.dtor_arguments;
            RAST._IType _4_dt__update__tmp_h0 = this;
            Dafny.ISequence<RAST._IType> _5_dt__update_harguments_h0 = Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(Dafny.Helpers.Id<Func<Func<RAST._IType, RAST._IType>, Dafny.ISequence<RAST._IType>, Func<RAST._IType, RAST._IType>>>((_6_mapping, _7_arguments) => ((System.Func<RAST._IType, RAST._IType>)((_8_t) => {
              return (_8_t).Replace(_6_mapping);
            })))(mapping, _3_arguments), _3_arguments);
            RAST._IType _9_dt__update_hbaseName_h0 = (_2_baseName).Replace(mapping);
            return RAST.Type.create_TypeApp(_9_dt__update_hbaseName_h0, _5_dt__update_harguments_h0);
          }
        }
        {
          if (_source0.is_Borrowed) {
            RAST._IType _10_underlying = _source0.dtor_underlying;
            RAST._IType _11_dt__update__tmp_h1 = this;
            RAST._IType _12_dt__update_hunderlying_h0 = (_10_underlying).Replace(mapping);
            if ((_11_dt__update__tmp_h1).is_Borrowed) {
              return RAST.Type.create_Borrowed(_12_dt__update_hunderlying_h0);
            } else if ((_11_dt__update__tmp_h1).is_BorrowedMut) {
              return RAST.Type.create_BorrowedMut(_12_dt__update_hunderlying_h0);
            } else if ((_11_dt__update__tmp_h1).is_ImplType) {
              return RAST.Type.create_ImplType(_12_dt__update_hunderlying_h0);
            } else if ((_11_dt__update__tmp_h1).is_DynType) {
              return RAST.Type.create_DynType(_12_dt__update_hunderlying_h0);
            } else {
              return RAST.Type.create_Array(_12_dt__update_hunderlying_h0, (_11_dt__update__tmp_h1).dtor_size);
            }
          }
        }
        {
          if (_source0.is_BorrowedMut) {
            RAST._IType _13_underlying = _source0.dtor_underlying;
            RAST._IType _14_dt__update__tmp_h2 = this;
            RAST._IType _15_dt__update_hunderlying_h1 = (_13_underlying).Replace(mapping);
            if ((_14_dt__update__tmp_h2).is_Borrowed) {
              return RAST.Type.create_Borrowed(_15_dt__update_hunderlying_h1);
            } else if ((_14_dt__update__tmp_h2).is_BorrowedMut) {
              return RAST.Type.create_BorrowedMut(_15_dt__update_hunderlying_h1);
            } else if ((_14_dt__update__tmp_h2).is_ImplType) {
              return RAST.Type.create_ImplType(_15_dt__update_hunderlying_h1);
            } else if ((_14_dt__update__tmp_h2).is_DynType) {
              return RAST.Type.create_DynType(_15_dt__update_hunderlying_h1);
            } else {
              return RAST.Type.create_Array(_15_dt__update_hunderlying_h1, (_14_dt__update__tmp_h2).dtor_size);
            }
          }
        }
        {
          if (_source0.is_ImplType) {
            RAST._IType _16_underlying = _source0.dtor_underlying;
            RAST._IType _17_dt__update__tmp_h3 = this;
            RAST._IType _18_dt__update_hunderlying_h2 = (_16_underlying).Replace(mapping);
            if ((_17_dt__update__tmp_h3).is_Borrowed) {
              return RAST.Type.create_Borrowed(_18_dt__update_hunderlying_h2);
            } else if ((_17_dt__update__tmp_h3).is_BorrowedMut) {
              return RAST.Type.create_BorrowedMut(_18_dt__update_hunderlying_h2);
            } else if ((_17_dt__update__tmp_h3).is_ImplType) {
              return RAST.Type.create_ImplType(_18_dt__update_hunderlying_h2);
            } else if ((_17_dt__update__tmp_h3).is_DynType) {
              return RAST.Type.create_DynType(_18_dt__update_hunderlying_h2);
            } else {
              return RAST.Type.create_Array(_18_dt__update_hunderlying_h2, (_17_dt__update__tmp_h3).dtor_size);
            }
          }
        }
        {
          if (_source0.is_DynType) {
            RAST._IType _19_underlying = _source0.dtor_underlying;
            RAST._IType _20_dt__update__tmp_h4 = this;
            RAST._IType _21_dt__update_hunderlying_h3 = (_19_underlying).Replace(mapping);
            if ((_20_dt__update__tmp_h4).is_Borrowed) {
              return RAST.Type.create_Borrowed(_21_dt__update_hunderlying_h3);
            } else if ((_20_dt__update__tmp_h4).is_BorrowedMut) {
              return RAST.Type.create_BorrowedMut(_21_dt__update_hunderlying_h3);
            } else if ((_20_dt__update__tmp_h4).is_ImplType) {
              return RAST.Type.create_ImplType(_21_dt__update_hunderlying_h3);
            } else if ((_20_dt__update__tmp_h4).is_DynType) {
              return RAST.Type.create_DynType(_21_dt__update_hunderlying_h3);
            } else {
              return RAST.Type.create_Array(_21_dt__update_hunderlying_h3, (_20_dt__update__tmp_h4).dtor_size);
            }
          }
        }
        {
          if (_source0.is_TupleType) {
            Dafny.ISequence<RAST._IType> _22_arguments = _source0.dtor_arguments;
            RAST._IType _23_dt__update__tmp_h5 = this;
            Dafny.ISequence<RAST._IType> _24_dt__update_harguments_h1 = Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(Dafny.Helpers.Id<Func<Func<RAST._IType, RAST._IType>, Dafny.ISequence<RAST._IType>, Func<RAST._IType, RAST._IType>>>((_25_mapping, _26_arguments) => ((System.Func<RAST._IType, RAST._IType>)((_27_t) => {
              return (_27_t).Replace(_25_mapping);
            })))(mapping, _22_arguments), _22_arguments);
            if ((_23_dt__update__tmp_h5).is_TypeApp) {
              return RAST.Type.create_TypeApp((_23_dt__update__tmp_h5).dtor_baseName, _24_dt__update_harguments_h1);
            } else if ((_23_dt__update__tmp_h5).is_TupleType) {
              return RAST.Type.create_TupleType(_24_dt__update_harguments_h1);
            } else {
              return RAST.Type.create_FnType(_24_dt__update_harguments_h1, (_23_dt__update__tmp_h5).dtor_returnType);
            }
          }
        }
        {
          if (_source0.is_FnType) {
            Dafny.ISequence<RAST._IType> _28_arguments = _source0.dtor_arguments;
            RAST._IType _29_returnType = _source0.dtor_returnType;
            RAST._IType _30_dt__update__tmp_h6 = this;
            RAST._IType _31_dt__update_hreturnType_h0 = (_29_returnType).Replace(mapping);
            Dafny.ISequence<RAST._IType> _32_dt__update_harguments_h2 = Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(Dafny.Helpers.Id<Func<Func<RAST._IType, RAST._IType>, Dafny.ISequence<RAST._IType>, Func<RAST._IType, RAST._IType>>>((_33_mapping, _34_arguments) => ((System.Func<RAST._IType, RAST._IType>)((_35_t) => {
              return (_35_t).Replace(_33_mapping);
            })))(mapping, _28_arguments), _28_arguments);
            return RAST.Type.create_FnType(_32_dt__update_harguments_h2, _31_dt__update_hreturnType_h0);
          }
        }
        {
          if (_source0.is_IntersectionType) {
            RAST._IType _36_left = _source0.dtor_left;
            RAST._IType _37_right = _source0.dtor_right;
            RAST._IType _38_dt__update__tmp_h7 = this;
            RAST._IType _39_dt__update_hright_h0 = (_37_right).Replace(mapping);
            RAST._IType _40_dt__update_hleft_h0 = (_36_left).Replace(mapping);
            return RAST.Type.create_IntersectionType(_40_dt__update_hleft_h0, _39_dt__update_hright_h0);
          }
        }
        {
          if (_source0.is_Array) {
            RAST._IType _41_underlying = _source0.dtor_underlying;
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _42_size = _source0.dtor_size;
            RAST._IType _43_dt__update__tmp_h8 = this;
            RAST._IType _44_dt__update_hunderlying_h4 = (_41_underlying).Replace(mapping);
            if ((_43_dt__update__tmp_h8).is_Borrowed) {
              return RAST.Type.create_Borrowed(_44_dt__update_hunderlying_h4);
            } else if ((_43_dt__update__tmp_h8).is_BorrowedMut) {
              return RAST.Type.create_BorrowedMut(_44_dt__update_hunderlying_h4);
            } else if ((_43_dt__update__tmp_h8).is_ImplType) {
              return RAST.Type.create_ImplType(_44_dt__update_hunderlying_h4);
            } else if ((_43_dt__update__tmp_h8).is_DynType) {
              return RAST.Type.create_DynType(_44_dt__update_hunderlying_h4);
            } else {
              return RAST.Type.create_Array(_44_dt__update_hunderlying_h4, (_43_dt__update__tmp_h8).dtor_size);
            }
          }
        }
        {
          if (_source0.is_TSynonym) {
            RAST._IType _45_display = _source0.dtor_display;
            RAST._IType _46_base = _source0.dtor_base;
            RAST._IType _47_dt__update__tmp_h9 = this;
            RAST._IType _48_dt__update_hbase_h0 = (_46_base).Replace(mapping);
            RAST._IType _49_dt__update_hdisplay_h0 = (_45_display).Replace(mapping);
            return RAST.Type.create_TSynonym(_49_dt__update_hdisplay_h0, _48_dt__update_hbase_h0);
          }
        }
        {
          RAST._IType _50_display = _source0.dtor_display;
          bool _51_copySemantics = _source0.dtor_copySemantics;
          bool _52_overflow = _source0.dtor_overflow;
          RAST._IType _53_dt__update__tmp_h10 = this;
          RAST._IType _54_dt__update_hdisplay_h1 = (_50_display).Replace(mapping);
          if ((_53_dt__update__tmp_h10).is_TSynonym) {
            return RAST.Type.create_TSynonym(_54_dt__update_hdisplay_h1, (_53_dt__update__tmp_h10).dtor_base);
          } else {
            return RAST.Type.create_TMetaData(_54_dt__update_hdisplay_h1, (_53_dt__update__tmp_h10).dtor_copySemantics, (_53_dt__update__tmp_h10).dtor_overflow);
          }
        }
      }))();
      return Dafny.Helpers.Id<Func<RAST._IType, RAST._IType>>(mapping)(_0_r);
    }
    public __T Fold<__T>(__T acc, Func<__T, RAST._IType, __T> f)
    {
      __T _0_newAcc = Dafny.Helpers.Id<Func<__T, RAST._IType, __T>>(f)(acc, this);
      RAST._IType _source0 = this;
      {
        bool disjunctiveMatch0 = false;
        if (_source0.is_U8) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_U16) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_U32) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_U64) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_U128) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_I8) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_I16) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_I32) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_I64) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_I128) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_USIZE) {
          disjunctiveMatch0 = true;
        }
        if (_source0.is_Bool) {
          disjunctiveMatch0 = true;
        }
        if (disjunctiveMatch0) {
          return _0_newAcc;
        }
      }
      {
        if (_source0.is_TIdentifier) {
          return _0_newAcc;
        }
      }
      {
        if (_source0.is_TypeFromPath) {
          RAST._IPath _1_path = _source0.dtor_path;
          return _0_newAcc;
        }
      }
      {
        if (_source0.is_TypeApp) {
          RAST._IType _2_baseName = _source0.dtor_baseName;
          Dafny.ISequence<RAST._IType> _3_arguments = _source0.dtor_arguments;
          __T _4_newAcc = (_2_baseName).Fold<__T>(_0_newAcc, f);
          return RAST.__default.FoldLeft<__T, RAST._IType>(Dafny.Helpers.Id<Func<Func<__T, RAST._IType, __T>, Dafny.ISequence<RAST._IType>, Func<__T, RAST._IType, __T>>>((_5_f, _6_arguments) => ((System.Func<__T, RAST._IType, __T>)((_7_acc, _8_argType) => {
            return (_8_argType).Fold<__T>(_7_acc, _5_f);
          })))(f, _3_arguments), _4_newAcc, _3_arguments);
        }
      }
      {
        if (_source0.is_Borrowed) {
          RAST._IType _9_underlying = _source0.dtor_underlying;
          return (_9_underlying).Fold<__T>(_0_newAcc, f);
        }
      }
      {
        if (_source0.is_BorrowedMut) {
          RAST._IType _10_underlying = _source0.dtor_underlying;
          return (_10_underlying).Fold<__T>(_0_newAcc, f);
        }
      }
      {
        if (_source0.is_ImplType) {
          RAST._IType _11_underlying = _source0.dtor_underlying;
          return (_11_underlying).Fold<__T>(_0_newAcc, f);
        }
      }
      {
        if (_source0.is_DynType) {
          RAST._IType _12_underlying = _source0.dtor_underlying;
          return (_12_underlying).Fold<__T>(_0_newAcc, f);
        }
      }
      {
        if (_source0.is_TupleType) {
          Dafny.ISequence<RAST._IType> _13_arguments = _source0.dtor_arguments;
          return RAST.__default.FoldLeft<__T, RAST._IType>(Dafny.Helpers.Id<Func<Func<__T, RAST._IType, __T>, Dafny.ISequence<RAST._IType>, Func<__T, RAST._IType, __T>>>((_14_f, _15_arguments) => ((System.Func<__T, RAST._IType, __T>)((_16_acc, _17_argType) => {
            return (_17_argType).Fold<__T>(_16_acc, _14_f);
          })))(f, _13_arguments), _0_newAcc, _13_arguments);
        }
      }
      {
        if (_source0.is_FnType) {
          Dafny.ISequence<RAST._IType> _18_arguments = _source0.dtor_arguments;
          RAST._IType _19_returnType = _source0.dtor_returnType;
          return (_19_returnType).Fold<__T>(RAST.__default.FoldLeft<__T, RAST._IType>(Dafny.Helpers.Id<Func<Func<__T, RAST._IType, __T>, Dafny.ISequence<RAST._IType>, Func<__T, RAST._IType, __T>>>((_20_f, _21_arguments) => ((System.Func<__T, RAST._IType, __T>)((_22_acc, _23_argType) => {
            return (_23_argType).Fold<__T>(_22_acc, _20_f);
          })))(f, _18_arguments), _0_newAcc, _18_arguments), f);
        }
      }
      {
        if (_source0.is_IntersectionType) {
          RAST._IType _24_left = _source0.dtor_left;
          RAST._IType _25_right = _source0.dtor_right;
          return (_25_right).Fold<__T>((_24_left).Fold<__T>(_0_newAcc, f), f);
        }
      }
      {
        if (_source0.is_Array) {
          RAST._IType _26_underlying = _source0.dtor_underlying;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _27_size = _source0.dtor_size;
          return (_26_underlying).Fold<__T>(_0_newAcc, f);
        }
      }
      {
        if (_source0.is_TSynonym) {
          RAST._IType _28_display = _source0.dtor_display;
          RAST._IType _29_base = _source0.dtor_base;
          return (_28_display).Fold<__T>(_0_newAcc, f);
        }
      }
      {
        RAST._IType _30_display = _source0.dtor_display;
        return (_30_display).Fold<__T>(_0_newAcc, f);
      }
    }
    public bool IsAutoSize() {
      return (((((((((((((this).is_U8) || ((this).is_U16)) || ((this).is_U32)) || ((this).is_U64)) || ((this).is_U128)) || ((this).is_I8)) || ((this).is_I16)) || ((this).is_I32)) || ((this).is_I64)) || ((this).is_I128)) || ((this).is_USIZE)) || (((this).is_TSynonym) && (((this).dtor_base).IsAutoSize()))) || (((this).is_TMetaData) && (((this).dtor_display).IsAutoSize()));
    }
    public bool CanReadWithoutClone() {
      return (((((this).IsAutoSize()) || ((this).is_Bool)) || ((this).IsPointer())) || (((this).is_TSynonym) && (((this).dtor_base).CanReadWithoutClone()))) || (((this).is_TMetaData) && (((this).dtor_copySemantics) || (((this).dtor_display).CanReadWithoutClone())));
    }
    public bool IsRcOrBorrowedRc() {
      return (((this).IsRc()) || (((this).is_Borrowed) && (((this).dtor_underlying).IsRcOrBorrowedRc()))) || (((this).is_TSynonym) && (((this).dtor_base).IsRcOrBorrowedRc()));
    }
    public Std.Wrappers._IOption<RAST._IType> ExtractMaybePlacebo() {
      RAST._IType _source0 = this;
      {
        if (_source0.is_TypeApp) {
          RAST._IType _0_wrapper = _source0.dtor_baseName;
          Dafny.ISequence<RAST._IType> _1_arguments = _source0.dtor_arguments;
          if ((object.Equals(_0_wrapper, RAST.Type.create_TypeFromPath(RAST.__default.MaybePlaceboPath))) && ((new BigInteger((_1_arguments).Count)) == (BigInteger.One))) {
            return Std.Wrappers.Option<RAST._IType>.create_Some((_1_arguments).Select(BigInteger.Zero));
          } else {
            return Std.Wrappers.Option<RAST._IType>.create_None();
          }
        }
      }
      {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
    }
    public Std.Wrappers._IOption<RAST._IType> ExtractMaybeUninitArrayElement() {
      if ((this).IsObjectOrPointer()) {
        RAST._IType _0_s = (this).ObjectOrPointerUnderlying();
        if (((_0_s).is_Array) && (RAST.__default.IsMaybeUninitType((_0_s).dtor_underlying))) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.MaybeUninitTypeUnderlying((_0_s).dtor_underlying));
        } else if (((_0_s).IsMultiArray()) && (RAST.__default.IsMaybeUninitType((_0_s).MultiArrayUnderlying()))) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.MaybeUninitTypeUnderlying((_0_s).MultiArrayUnderlying()));
        } else {
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      } else {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      RAST._IType _source0 = this;
      {
        if (_source0.is_Bool) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("bool");
        }
      }
      {
        if (_source0.is_TIdentifier) {
          Dafny.ISequence<Dafny.Rune> _0_underlying = _source0.dtor_name;
          return _0_underlying;
        }
      }
      {
        if (_source0.is_TypeFromPath) {
          RAST._IPath _1_underlying = _source0.dtor_path;
          return (_1_underlying)._ToString();
        }
      }
      {
        if (_source0.is_Borrowed) {
          RAST._IType _2_underlying = _source0.dtor_underlying;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), (_2_underlying)._ToString(ind));
        }
      }
      {
        if (_source0.is_BorrowedMut) {
          RAST._IType _3_underlying = _source0.dtor_underlying;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut "), (_3_underlying)._ToString(ind));
        }
      }
      {
        if (_source0.is_ImplType) {
          RAST._IType _4_underlying = _source0.dtor_underlying;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl "), (_4_underlying)._ToString(ind));
        }
      }
      {
        if (_source0.is_DynType) {
          RAST._IType _5_underlying = _source0.dtor_underlying;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn "), (_5_underlying)._ToString(ind));
        }
      }
      {
        if (_source0.is_FnType) {
          Dafny.ISequence<RAST._IType> _6_arguments = _source0.dtor_arguments;
          RAST._IType _7_returnType = _source0.dtor_returnType;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Fn("), RAST.__default.SeqToString<RAST._IType>(_6_arguments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_8_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_9_arg) => {
            return (_9_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_8_ind, RAST.__default.IND));
          })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> ")), (_7_returnType)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)));
        }
      }
      {
        if (_source0.is_IntersectionType) {
          RAST._IType _10_left = _source0.dtor_left;
          RAST._IType _11_right = _source0.dtor_right;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_10_left)._ToString(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + ")), (_11_right)._ToString(ind));
        }
      }
      {
        if (_source0.is_TupleType) {
          Dafny.ISequence<RAST._IType> _12_args = _source0.dtor_arguments;
          if ((_12_args).Equals(Dafny.Sequence<RAST._IType>.FromElements())) {
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()");
          } else {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<RAST._IType>(_12_args, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_13_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_14_arg) => {
              return (_14_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_13_ind, RAST.__default.IND));
            })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          }
        }
      }
      {
        if (_source0.is_TypeApp) {
          RAST._IType _15_base = _source0.dtor_baseName;
          Dafny.ISequence<RAST._IType> _16_args = _source0.dtor_arguments;
          return Dafny.Sequence<Dafny.Rune>.Concat((_15_base)._ToString(ind), (((_16_args).Equals(Dafny.Sequence<RAST._IType>.FromElements())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), RAST.__default.SeqToString<RAST._IType>(_16_args, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_17_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_18_arg) => {
            return (_18_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_17_ind, RAST.__default.IND));
          })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">")))));
        }
      }
      {
        if (_source0.is_U8) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u8");
        }
      }
      {
        if (_source0.is_U16) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u16");
        }
      }
      {
        if (_source0.is_U32) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u32");
        }
      }
      {
        if (_source0.is_U64) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u64");
        }
      }
      {
        if (_source0.is_U128) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u128");
        }
      }
      {
        if (_source0.is_I8) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i8");
        }
      }
      {
        if (_source0.is_I16) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i16");
        }
      }
      {
        if (_source0.is_I32) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i32");
        }
      }
      {
        if (_source0.is_I64) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i64");
        }
      }
      {
        if (_source0.is_I128) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i128");
        }
      }
      {
        if (_source0.is_USIZE) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("usize");
        }
      }
      {
        if (_source0.is_Array) {
          RAST._IType _19_underlying = _source0.dtor_underlying;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _20_size = _source0.dtor_size;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("["), (_19_underlying)._ToString(ind)), (((_20_size).is_Some) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("; "), (_20_size).dtor_value)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
        }
      }
      {
        if (_source0.is_TSynonym) {
          RAST._IType _21_display = _source0.dtor_display;
          RAST._IType _22_base = _source0.dtor_base;
          return (_21_display)._ToString(ind);
        }
      }
      {
        RAST._IType _23_display = _source0.dtor_display;
        return (_23_display)._ToString(ind);
      }
    }
    public RAST._IType Apply1(RAST._IType arg) {
      return RAST.Type.create_TypeApp(this, Dafny.Sequence<RAST._IType>.FromElements(arg));
    }
    public RAST._IType Apply(Dafny.ISequence<RAST._IType> args) {
      return RAST.Type.create_TypeApp(this, args);
    }
    public RAST._IType ToOwned() {
      RAST._IType _source0 = this;
      {
        if (_source0.is_Borrowed) {
          RAST._IType _0_x = _source0.dtor_underlying;
          return _0_x;
        }
      }
      {
        if (_source0.is_BorrowedMut) {
          RAST._IType _1_x = _source0.dtor_underlying;
          return _1_x;
        }
      }
      {
        RAST._IType _2_x = _source0;
        return _2_x;
      }
    }
    public RAST._IExpr ToNullExpr() {
      if (((this).Expand()).IsObject()) {
        return ((RAST.__default.Object).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"))).Apply0();
      } else {
        return ((RAST.__default.Ptr).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"))).Apply0();
      }
    }
    public bool IsMultiArray() {
      RAST._IType _0_t = (this).Expand();
      return ((_0_t).is_TypeApp) && (Dafny.Helpers.Let<RAST._IType, bool>((_0_t).dtor_baseName, _pat_let65_0 => Dafny.Helpers.Let<RAST._IType, bool>(_pat_let65_0, _1_baseName => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, bool>((_0_t).dtor_arguments, _pat_let66_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, bool>(_pat_let66_0, _2_args => ((((((new BigInteger((_2_args).Count)) == (BigInteger.One)) && ((_1_baseName).is_TypeFromPath)) && (((_1_baseName).dtor_path).is_PMemberSelect)) && (object.Equals(((_1_baseName).dtor_path).dtor_base, RAST.__default.dafny__runtime))) && ((new BigInteger((((_1_baseName).dtor_path).dtor_name).Count)) >= (new BigInteger(5)))) && (((((_1_baseName).dtor_path).dtor_name).Subsequence(BigInteger.Zero, new BigInteger(5))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"))))))));
    }
    public Dafny.ISequence<Dafny.Rune> MultiArrayClass() {
      return ((((this).Expand()).dtor_baseName).dtor_path).dtor_name;
    }
    public RAST._IType MultiArrayUnderlying() {
      return (((this).Expand()).dtor_arguments).Select(BigInteger.Zero);
    }
    public RAST._IType TypeAtInitialization() {
      if ((this).IsObjectOrPointer()) {
        RAST._IType _0_s = (this).ObjectOrPointerUnderlying();
        if (((_0_s).is_Array) && (((_0_s).dtor_size).is_None)) {
          RAST._IType _1_newUnderlying = RAST.Type.create_Array(RAST.__default.MaybeUninitType((_0_s).dtor_underlying), Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
          if ((this).IsObject()) {
            return RAST.__default.ObjectType(_1_newUnderlying);
          } else {
            return RAST.__default.PtrType(_1_newUnderlying);
          }
        } else if ((_0_s).IsMultiArray()) {
          RAST._IType _2_newUnderlying = RAST.Type.create_TypeApp(((_0_s).Expand()).dtor_baseName, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.MaybeUninitType((((_0_s).Expand()).dtor_arguments).Select(BigInteger.Zero))));
          if ((this).IsObject()) {
            return RAST.__default.ObjectType(_2_newUnderlying);
          } else {
            return RAST.__default.PtrType(_2_newUnderlying);
          }
        } else {
          return this;
        }
      } else {
        return this;
      }
    }
    public bool IsMaybeUninit() {
      return ((((this).is_TypeApp) && (((this).dtor_baseName).is_TypeFromPath)) && (object.Equals(((this).dtor_baseName).dtor_path, RAST.__default.MaybeUninitPath))) && ((new BigInteger(((this).dtor_arguments).Count)) == (BigInteger.One));
    }
    public bool IsUninitArray() {
      if ((this).IsObjectOrPointer()) {
        RAST._IType _0_s = ((this).ObjectOrPointerUnderlying()).Expand();
        if (((_0_s).is_Array) && (((_0_s).dtor_size).is_None)) {
          return ((_0_s).dtor_underlying).IsMaybeUninit();
        } else if ((_0_s).IsMultiArray()) {
          return (((_0_s).dtor_arguments).Select(BigInteger.Zero)).IsMaybeUninit();
        } else {
          return false;
        }
      } else {
        return false;
      }
    }
    public bool IsBox() {
      RAST._IType _source0 = this;
      {
        if (_source0.is_TypeApp) {
          RAST._IType baseName0 = _source0.dtor_baseName;
          if (baseName0.is_TypeFromPath) {
            RAST._IPath _0_o = baseName0.dtor_path;
            Dafny.ISequence<RAST._IType> _1_elems1 = _source0.dtor_arguments;
            return (object.Equals(_0_o, RAST.__default.BoxPath)) && ((new BigInteger((_1_elems1).Count)) == (BigInteger.One));
          }
        }
      }
      {
        return false;
      }
    }
    public bool NeedsAsRefForBorrow() {
      if ((this).is_Borrowed) {
        return (((this).dtor_underlying).IsBox()) || (((this).dtor_underlying).IsRc());
      } else {
        return ((this).IsBox()) || ((this).IsRc());
      }
    }
    public RAST._IType BoxUnderlying() {
      RAST._IType _source0 = this;
      {
        RAST._IType baseName0 = _source0.dtor_baseName;
        RAST._IPath _0_o = baseName0.dtor_path;
        Dafny.ISequence<RAST._IType> _1_elems1 = _source0.dtor_arguments;
        return (_1_elems1).Select(BigInteger.Zero);
      }
    }
    public bool IsObject() {
      RAST._IType _source0 = this;
      {
        if (_source0.is_TypeApp) {
          RAST._IType baseName0 = _source0.dtor_baseName;
          if (baseName0.is_TypeFromPath) {
            RAST._IPath _0_o = baseName0.dtor_path;
            Dafny.ISequence<RAST._IType> _1_elems1 = _source0.dtor_arguments;
            return (object.Equals(_0_o, RAST.__default.ObjectPath)) && ((new BigInteger((_1_elems1).Count)) == (BigInteger.One));
          }
        }
      }
      {
        return false;
      }
    }
    public bool IsPointer() {
      RAST._IType _source0 = this;
      {
        if (_source0.is_TypeApp) {
          RAST._IType baseName0 = _source0.dtor_baseName;
          if (baseName0.is_TypeFromPath) {
            RAST._IPath _0_o = baseName0.dtor_path;
            Dafny.ISequence<RAST._IType> _1_elems1 = _source0.dtor_arguments;
            return (object.Equals(_0_o, RAST.__default.PtrPath)) && ((new BigInteger((_1_elems1).Count)) == (BigInteger.One));
          }
        }
      }
      {
        return false;
      }
    }
    public bool IsObjectOrPointer()
    {
      bool _hresult = false;
      RAST._IType _0_t;
      _0_t = (this).Expand();
      _hresult = ((_0_t).IsPointer()) || ((_0_t).IsObject());
      return _hresult;
      return _hresult;
    }
    public RAST._IType ObjectOrPointerUnderlying() {
      RAST._IType _source0 = (this).Expand();
      {
        Dafny.ISequence<RAST._IType> _0_elems1 = _source0.dtor_arguments;
        return (_0_elems1).Select(BigInteger.Zero);
      }
    }
    public bool IsBuiltinCollection() {
      RAST._IType _source0 = (this).Expand();
      {
        if (_source0.is_TypeApp) {
          RAST._IType baseName0 = _source0.dtor_baseName;
          if (baseName0.is_TypeFromPath) {
            RAST._IPath path0 = baseName0.dtor_path;
            if (path0.is_PMemberSelect) {
              RAST._IPath base0 = path0.dtor_base;
              if (base0.is_PMemberSelect) {
                RAST._IPath base1 = base0.dtor_base;
                if (base1.is_Global) {
                  Dafny.ISequence<Dafny.Rune> name0 = base0.dtor_name;
                  if (object.Equals(name0, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dafny_runtime"))) {
                    Dafny.ISequence<Dafny.Rune> _0_tpe = path0.dtor_name;
                    Dafny.ISequence<RAST._IType> _1_elems1 = _source0.dtor_arguments;
                    return (((((_0_tpe).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set"))) || ((_0_tpe).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")))) || ((_0_tpe).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")))) && ((new BigInteger((_1_elems1).Count)) == (BigInteger.One))) || (((_0_tpe).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) && ((new BigInteger((_1_elems1).Count)) == (new BigInteger(2))));
                  }
                }
              }
            }
          }
        }
      }
      {
        return false;
      }
    }
    public RAST._IType GetBuiltinCollectionElement() {
      RAST._IType _source0 = (this).Expand();
      {
        RAST._IType baseName0 = _source0.dtor_baseName;
        RAST._IPath path0 = baseName0.dtor_path;
        RAST._IPath base0 = path0.dtor_base;
        RAST._IPath base1 = base0.dtor_base;
        Dafny.ISequence<Dafny.Rune> name0 = base0.dtor_name;
        Dafny.ISequence<Dafny.Rune> _0_tpe = path0.dtor_name;
        Dafny.ISequence<RAST._IType> _1_elems = _source0.dtor_arguments;
        if ((_0_tpe).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) {
          return (_1_elems).Select(BigInteger.One);
        } else {
          return (_1_elems).Select(BigInteger.Zero);
        }
      }
    }
    public bool IsRc() {
      return (((this).is_TypeApp) && ((object.Equals((this).dtor_baseName, RAST.__default.RcType)) || (object.Equals((this).dtor_baseName, RAST.__default.ArcType)))) && ((new BigInteger(((this).dtor_arguments).Count)) == (BigInteger.One));
    }
    public RAST._IType RcUnderlying() {
      return ((this).dtor_arguments).Select(BigInteger.Zero);
    }
    public bool IsBoxDyn() {
      return ((((this).is_TypeApp) && (object.Equals((this).dtor_baseName, RAST.__default.BoxType))) && ((new BigInteger(((this).dtor_arguments).Count)) == (BigInteger.One))) && ((((this).dtor_arguments).Select(BigInteger.Zero)).is_DynType);
    }
    public RAST._IType BoxDynUnderlying() {
      return (((this).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying;
    }
  }
  public class Type_U8 : Type {
    public Type_U8() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_U8();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_U8;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.U8";
      return s;
    }
  }
  public class Type_U16 : Type {
    public Type_U16() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_U16();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_U16;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.U16";
      return s;
    }
  }
  public class Type_U32 : Type {
    public Type_U32() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_U32();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_U32;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.U32";
      return s;
    }
  }
  public class Type_U64 : Type {
    public Type_U64() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_U64();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_U64;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.U64";
      return s;
    }
  }
  public class Type_U128 : Type {
    public Type_U128() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_U128();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_U128;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.U128";
      return s;
    }
  }
  public class Type_I8 : Type {
    public Type_I8() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_I8();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_I8;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.I8";
      return s;
    }
  }
  public class Type_I16 : Type {
    public Type_I16() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_I16();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_I16;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.I16";
      return s;
    }
  }
  public class Type_I32 : Type {
    public Type_I32() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_I32();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_I32;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.I32";
      return s;
    }
  }
  public class Type_I64 : Type {
    public Type_I64() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_I64();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_I64;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.I64";
      return s;
    }
  }
  public class Type_I128 : Type {
    public Type_I128() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_I128();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_I128;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.I128";
      return s;
    }
  }
  public class Type_USIZE : Type {
    public Type_USIZE() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_USIZE();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_USIZE;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.USIZE";
      return s;
    }
  }
  public class Type_Bool : Type {
    public Type_Bool() : base() {
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Bool();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_Bool;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.Bool";
      return s;
    }
  }
  public class Type_TIdentifier : Type {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public Type_TIdentifier(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._name = name;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TIdentifier(_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TIdentifier;
      return oth != null && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TIdentifier";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Type_TypeFromPath : Type {
    public readonly RAST._IPath _path;
    public Type_TypeFromPath(RAST._IPath path) : base() {
      this._path = path;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TypeFromPath(_path);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TypeFromPath;
      return oth != null && object.Equals(this._path, oth._path);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._path));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TypeFromPath";
      s += "(";
      s += Dafny.Helpers.ToString(this._path);
      s += ")";
      return s;
    }
  }
  public class Type_TypeApp : Type {
    public readonly RAST._IType _baseName;
    public readonly Dafny.ISequence<RAST._IType> _arguments;
    public Type_TypeApp(RAST._IType baseName, Dafny.ISequence<RAST._IType> arguments) : base() {
      this._baseName = baseName;
      this._arguments = arguments;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TypeApp(_baseName, _arguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TypeApp;
      return oth != null && object.Equals(this._baseName, oth._baseName) && object.Equals(this._arguments, oth._arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._baseName));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TypeApp";
      s += "(";
      s += Dafny.Helpers.ToString(this._baseName);
      s += ", ";
      s += Dafny.Helpers.ToString(this._arguments);
      s += ")";
      return s;
    }
  }
  public class Type_Borrowed : Type {
    public readonly RAST._IType _underlying;
    public Type_Borrowed(RAST._IType underlying) : base() {
      this._underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Borrowed(_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_Borrowed;
      return oth != null && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.Borrowed";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Type_BorrowedMut : Type {
    public readonly RAST._IType _underlying;
    public Type_BorrowedMut(RAST._IType underlying) : base() {
      this._underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_BorrowedMut(_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_BorrowedMut;
      return oth != null && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.BorrowedMut";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Type_ImplType : Type {
    public readonly RAST._IType _underlying;
    public Type_ImplType(RAST._IType underlying) : base() {
      this._underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_ImplType(_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_ImplType;
      return oth != null && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.ImplType";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Type_DynType : Type {
    public readonly RAST._IType _underlying;
    public Type_DynType(RAST._IType underlying) : base() {
      this._underlying = underlying;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_DynType(_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_DynType;
      return oth != null && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.DynType";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Type_TupleType : Type {
    public readonly Dafny.ISequence<RAST._IType> _arguments;
    public Type_TupleType(Dafny.ISequence<RAST._IType> arguments) : base() {
      this._arguments = arguments;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TupleType(_arguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TupleType;
      return oth != null && object.Equals(this._arguments, oth._arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 19;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TupleType";
      s += "(";
      s += Dafny.Helpers.ToString(this._arguments);
      s += ")";
      return s;
    }
  }
  public class Type_FnType : Type {
    public readonly Dafny.ISequence<RAST._IType> _arguments;
    public readonly RAST._IType _returnType;
    public Type_FnType(Dafny.ISequence<RAST._IType> arguments, RAST._IType returnType) : base() {
      this._arguments = arguments;
      this._returnType = returnType;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_FnType(_arguments, _returnType);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_FnType;
      return oth != null && object.Equals(this._arguments, oth._arguments) && object.Equals(this._returnType, oth._returnType);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 20;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arguments));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._returnType));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.FnType";
      s += "(";
      s += Dafny.Helpers.ToString(this._arguments);
      s += ", ";
      s += Dafny.Helpers.ToString(this._returnType);
      s += ")";
      return s;
    }
  }
  public class Type_IntersectionType : Type {
    public readonly RAST._IType _left;
    public readonly RAST._IType _right;
    public Type_IntersectionType(RAST._IType left, RAST._IType right) : base() {
      this._left = left;
      this._right = right;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_IntersectionType(_left, _right);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_IntersectionType;
      return oth != null && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 21;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.IntersectionType";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ")";
      return s;
    }
  }
  public class Type_Array : Type {
    public readonly RAST._IType _underlying;
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _size;
    public Type_Array(RAST._IType underlying, Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> size) : base() {
      this._underlying = underlying;
      this._size = size;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_Array(_underlying, _size);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_Array;
      return oth != null && object.Equals(this._underlying, oth._underlying) && object.Equals(this._size, oth._size);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 22;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._size));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.Array";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ", ";
      s += Dafny.Helpers.ToString(this._size);
      s += ")";
      return s;
    }
  }
  public class Type_TSynonym : Type {
    public readonly RAST._IType _display;
    public readonly RAST._IType _base;
    public Type_TSynonym(RAST._IType display, RAST._IType @base) : base() {
      this._display = display;
      this._base = @base;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TSynonym(_display, _base);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TSynonym;
      return oth != null && object.Equals(this._display, oth._display) && object.Equals(this._base, oth._base);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 23;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._display));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._base));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TSynonym";
      s += "(";
      s += Dafny.Helpers.ToString(this._display);
      s += ", ";
      s += Dafny.Helpers.ToString(this._base);
      s += ")";
      return s;
    }
  }
  public class Type_TMetaData : Type {
    public readonly RAST._IType _display;
    public readonly bool _copySemantics;
    public readonly bool _overflow;
    public Type_TMetaData(RAST._IType display, bool copySemantics, bool overflow) : base() {
      this._display = display;
      this._copySemantics = copySemantics;
      this._overflow = overflow;
    }
    public override _IType DowncastClone() {
      if (this is _IType dt) { return dt; }
      return new Type_TMetaData(_display, _copySemantics, _overflow);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Type_TMetaData;
      return oth != null && object.Equals(this._display, oth._display) && this._copySemantics == oth._copySemantics && this._overflow == oth._overflow;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 24;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._display));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._copySemantics));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overflow));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Type.TMetaData";
      s += "(";
      s += Dafny.Helpers.ToString(this._display);
      s += ", ";
      s += Dafny.Helpers.ToString(this._copySemantics);
      s += ", ";
      s += Dafny.Helpers.ToString(this._overflow);
      s += ")";
      return s;
    }
  }

  public interface _ITrait {
    bool is_Trait { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<RAST._IAttribute> dtor_attributes { get; }
    Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams { get; }
    RAST._IType dtor_tpe { get; }
    Dafny.ISequence<RAST._IType> dtor_parents { get; }
    Dafny.ISequence<RAST._IImplMember> dtor_body { get; }
    _ITrait DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Trait : _ITrait {
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<RAST._IAttribute> _attributes;
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly RAST._IType _tpe;
    public readonly Dafny.ISequence<RAST._IType> _parents;
    public readonly Dafny.ISequence<RAST._IImplMember> _body;
    public Trait(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, Dafny.ISequence<RAST._IType> parents, Dafny.ISequence<RAST._IImplMember> body) {
      this._docString = docString;
      this._attributes = attributes;
      this._typeParams = typeParams;
      this._tpe = tpe;
      this._parents = parents;
      this._body = body;
    }
    public _ITrait DowncastClone() {
      if (this is _ITrait dt) { return dt; }
      return new Trait(_docString, _attributes, _typeParams, _tpe, _parents, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Trait;
      return oth != null && object.Equals(this._docString, oth._docString) && object.Equals(this._attributes, oth._attributes) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._tpe, oth._tpe) && object.Equals(this._parents, oth._parents) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._parents));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Trait.Trait";
      s += "(";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ", ";
      s += Dafny.Helpers.ToString(this._parents);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
    private static readonly RAST._ITrait theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._IAttribute>.Empty, Dafny.Sequence<RAST._ITypeParamDecl>.Empty, RAST.Type.Default(), Dafny.Sequence<RAST._IType>.Empty, Dafny.Sequence<RAST._IImplMember>.Empty);
    public static RAST._ITrait Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._ITrait> _TYPE = new Dafny.TypeDescriptor<RAST._ITrait>(RAST.Trait.Default());
    public static Dafny.TypeDescriptor<RAST._ITrait> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITrait create(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, Dafny.ISequence<RAST._IType> parents, Dafny.ISequence<RAST._IImplMember> body) {
      return new Trait(docString, attributes, typeParams, tpe, parents, body);
    }
    public static _ITrait create_Trait(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, Dafny.ISequence<RAST._IType> parents, Dafny.ISequence<RAST._IImplMember> body) {
      return create(docString, attributes, typeParams, tpe, parents, body);
    }
    public bool is_Trait { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        return this._docString;
      }
    }
    public Dafny.ISequence<RAST._IAttribute> dtor_attributes {
      get {
        return this._attributes;
      }
    }
    public Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        return this._tpe;
      }
    }
    public Dafny.ISequence<RAST._IType> dtor_parents {
      get {
        return this._parents;
      }
    }
    public Dafny.ISequence<RAST._IImplMember> dtor_body {
      get {
        return this._body;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      Dafny.ISequence<RAST._ITypeParamDecl> _0_tpConstraints = Std.Collections.Seq.__default.Filter<RAST._ITypeParamDecl>(((System.Func<RAST._ITypeParamDecl, bool>)((_1_typeParamDecl) => {
        return (new BigInteger(((_1_typeParamDecl).dtor_constraints).Count)).Sign == 1;
      })), (this).dtor_typeParams);
      Dafny.ISequence<Dafny.Rune> _2_additionalConstraints = RAST.__default.SeqToString<RAST._ITypeParamDecl>(_0_tpConstraints, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._ITypeParamDecl, Dafny.ISequence<Dafny.Rune>>>>((_3_ind) => ((System.Func<RAST._ITypeParamDecl, Dafny.ISequence<Dafny.Rune>>)((_4_t) => {
        return (_4_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_3_ind, RAST.__default.IND));
      })))(ind), Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(",\n"), ind), RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _5_parents = (((new BigInteger(((this).dtor_parents).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": "), RAST.__default.SeqToString<RAST._IType>((this).dtor_parents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_6_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_7_t) => {
        return (_7_t)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_6_ind, RAST.__default.IND));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" + ")))));
      Dafny.ISequence<Dafny.Rune> _8_where = (((_2_additionalConstraints).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("where\n")), ind), RAST.__default.IND), _2_additionalConstraints)));
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.ToDocstringPrefix((this).dtor_docString, ind), RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub trait ")), ((this).dtor_tpe)._ToString(ind)), _5_parents), _8_where), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IImplMember>((this).dtor_body, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>>>((_9_ind) => ((System.Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>)((_10_member) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _9_ind), RAST.__default.IND), (_10_member)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_9_ind, RAST.__default.IND)));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (((new BigInteger(((this).dtor_body).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
    }
  }

  public interface _IImpl {
    bool is_ImplFor { get; }
    bool is_Impl { get; }
    Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams { get; }
    RAST._IType dtor_tpe { get; }
    RAST._IType dtor_forType { get; }
    Dafny.ISequence<RAST._IImplMember> dtor_body { get; }
    _IImpl DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public abstract class Impl : _IImpl {
    public Impl() {
    }
    private static readonly RAST._IImpl theDefault = create_ImplFor(Dafny.Sequence<RAST._ITypeParamDecl>.Empty, RAST.Type.Default(), RAST.Type.Default(), Dafny.Sequence<RAST._IImplMember>.Empty);
    public static RAST._IImpl Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IImpl> _TYPE = new Dafny.TypeDescriptor<RAST._IImpl>(RAST.Impl.Default());
    public static Dafny.TypeDescriptor<RAST._IImpl> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IImpl create_ImplFor(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, RAST._IType forType, Dafny.ISequence<RAST._IImplMember> body) {
      return new Impl_ImplFor(typeParams, tpe, forType, body);
    }
    public static _IImpl create_Impl(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, Dafny.ISequence<RAST._IImplMember> body) {
      return new Impl_Impl(typeParams, tpe, body);
    }
    public bool is_ImplFor { get { return this is Impl_ImplFor; } }
    public bool is_Impl { get { return this is Impl_Impl; } }
    public Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams {
      get {
        var d = this;
        if (d is Impl_ImplFor) { return ((Impl_ImplFor)d)._typeParams; }
        return ((Impl_Impl)d)._typeParams;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        var d = this;
        if (d is Impl_ImplFor) { return ((Impl_ImplFor)d)._tpe; }
        return ((Impl_Impl)d)._tpe;
      }
    }
    public RAST._IType dtor_forType {
      get {
        var d = this;
        return ((Impl_ImplFor)d)._forType;
      }
    }
    public Dafny.ISequence<RAST._IImplMember> dtor_body {
      get {
        var d = this;
        if (d is Impl_ImplFor) { return ((Impl_ImplFor)d)._body; }
        return ((Impl_Impl)d)._body;
      }
    }
    public abstract _IImpl DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl"), RAST.TypeParamDecl.ToStringMultiple((this).dtor_typeParams, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" ")), ((this).dtor_tpe)._ToString(ind)), (((this).is_ImplFor) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for ")), ((this).dtor_forType)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IImplMember>((this).dtor_body, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>>>((_0_ind) => ((System.Func<RAST._IImplMember, Dafny.ISequence<Dafny.Rune>>)((_1_member) => {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _0_ind), RAST.__default.IND), (_1_member)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_0_ind, RAST.__default.IND)));
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), (((new BigInteger(((this).dtor_body).Count)).Sign == 0) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
    }
  }
  public class Impl_ImplFor : Impl {
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly RAST._IType _tpe;
    public readonly RAST._IType _forType;
    public readonly Dafny.ISequence<RAST._IImplMember> _body;
    public Impl_ImplFor(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, RAST._IType forType, Dafny.ISequence<RAST._IImplMember> body) : base() {
      this._typeParams = typeParams;
      this._tpe = tpe;
      this._forType = forType;
      this._body = body;
    }
    public override _IImpl DowncastClone() {
      if (this is _IImpl dt) { return dt; }
      return new Impl_ImplFor(_typeParams, _tpe, _forType, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Impl_ImplFor;
      return oth != null && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._tpe, oth._tpe) && object.Equals(this._forType, oth._forType) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._forType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Impl.ImplFor";
      s += "(";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ", ";
      s += Dafny.Helpers.ToString(this._forType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }
  public class Impl_Impl : Impl {
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly RAST._IType _tpe;
    public readonly Dafny.ISequence<RAST._IImplMember> _body;
    public Impl_Impl(Dafny.ISequence<RAST._ITypeParamDecl> typeParams, RAST._IType tpe, Dafny.ISequence<RAST._IImplMember> body) : base() {
      this._typeParams = typeParams;
      this._tpe = tpe;
      this._body = body;
    }
    public override _IImpl DowncastClone() {
      if (this is _IImpl dt) { return dt; }
      return new Impl_Impl(_typeParams, _tpe, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Impl_Impl;
      return oth != null && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._tpe, oth._tpe) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Impl.Impl";
      s += "(";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }

  public interface _IImplMember {
    bool is_RawImplMember { get; }
    bool is_TypeDeclMember { get; }
    bool is_FnDecl { get; }
    bool is_ImplMemberMacro { get; }
    Dafny.ISequence<Dafny.Rune> dtor_content { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IType dtor_rhs { get; }
    Dafny.ISequence<Dafny.Rune> dtor_docString { get; }
    Dafny.ISequence<RAST._IAttribute> dtor_attributes { get; }
    RAST._IVisibility dtor_pub { get; }
    RAST._IFn dtor_fun { get; }
    RAST._IExpr dtor_expr { get; }
    _IImplMember DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public abstract class ImplMember : _IImplMember {
    public ImplMember() {
    }
    private static readonly RAST._IImplMember theDefault = create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Empty);
    public static RAST._IImplMember Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IImplMember> _TYPE = new Dafny.TypeDescriptor<RAST._IImplMember>(RAST.ImplMember.Default());
    public static Dafny.TypeDescriptor<RAST._IImplMember> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IImplMember create_RawImplMember(Dafny.ISequence<Dafny.Rune> content) {
      return new ImplMember_RawImplMember(content);
    }
    public static _IImplMember create_TypeDeclMember(Dafny.ISequence<Dafny.Rune> name, RAST._IType rhs) {
      return new ImplMember_TypeDeclMember(name, rhs);
    }
    public static _IImplMember create_FnDecl(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, RAST._IVisibility pub, RAST._IFn fun) {
      return new ImplMember_FnDecl(docString, attributes, pub, fun);
    }
    public static _IImplMember create_ImplMemberMacro(RAST._IExpr expr) {
      return new ImplMember_ImplMemberMacro(expr);
    }
    public bool is_RawImplMember { get { return this is ImplMember_RawImplMember; } }
    public bool is_TypeDeclMember { get { return this is ImplMember_TypeDeclMember; } }
    public bool is_FnDecl { get { return this is ImplMember_FnDecl; } }
    public bool is_ImplMemberMacro { get { return this is ImplMember_ImplMemberMacro; } }
    public Dafny.ISequence<Dafny.Rune> dtor_content {
      get {
        var d = this;
        return ((ImplMember_RawImplMember)d)._content;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        return ((ImplMember_TypeDeclMember)d)._name;
      }
    }
    public RAST._IType dtor_rhs {
      get {
        var d = this;
        return ((ImplMember_TypeDeclMember)d)._rhs;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_docString {
      get {
        var d = this;
        return ((ImplMember_FnDecl)d)._docString;
      }
    }
    public Dafny.ISequence<RAST._IAttribute> dtor_attributes {
      get {
        var d = this;
        return ((ImplMember_FnDecl)d)._attributes;
      }
    }
    public RAST._IVisibility dtor_pub {
      get {
        var d = this;
        return ((ImplMember_FnDecl)d)._pub;
      }
    }
    public RAST._IFn dtor_fun {
      get {
        var d = this;
        return ((ImplMember_FnDecl)d)._fun;
      }
    }
    public RAST._IExpr dtor_expr {
      get {
        var d = this;
        return ((ImplMember_ImplMemberMacro)d)._expr;
      }
    }
    public abstract _IImplMember DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      if ((this).is_FnDecl) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.ToDocstringPrefix((this).dtor_docString, ind), RAST.Attribute.ToStringMultiple((this).dtor_attributes, ind)), ((this).dtor_pub)._ToString()), ((this).dtor_fun)._ToString(ind));
      } else if ((this).is_ImplMemberMacro) {
        return Dafny.Sequence<Dafny.Rune>.Concat(((this).dtor_expr)._ToString(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
      } else if ((this).is_TypeDeclMember) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type "), (this).dtor_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), ((this).dtor_rhs)._ToString(ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
      } else {
        return (this).dtor_content;
      }
    }
  }
  public class ImplMember_RawImplMember : ImplMember {
    public readonly Dafny.ISequence<Dafny.Rune> _content;
    public ImplMember_RawImplMember(Dafny.ISequence<Dafny.Rune> content) : base() {
      this._content = content;
    }
    public override _IImplMember DowncastClone() {
      if (this is _IImplMember dt) { return dt; }
      return new ImplMember_RawImplMember(_content);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ImplMember_RawImplMember;
      return oth != null && object.Equals(this._content, oth._content);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._content));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ImplMember.RawImplMember";
      s += "(";
      s += this._content.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class ImplMember_TypeDeclMember : ImplMember {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly RAST._IType _rhs;
    public ImplMember_TypeDeclMember(Dafny.ISequence<Dafny.Rune> name, RAST._IType rhs) : base() {
      this._name = name;
      this._rhs = rhs;
    }
    public override _IImplMember DowncastClone() {
      if (this is _IImplMember dt) { return dt; }
      return new ImplMember_TypeDeclMember(_name, _rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ImplMember_TypeDeclMember;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._rhs, oth._rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ImplMember.TypeDeclMember";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rhs);
      s += ")";
      return s;
    }
  }
  public class ImplMember_FnDecl : ImplMember {
    public readonly Dafny.ISequence<Dafny.Rune> _docString;
    public readonly Dafny.ISequence<RAST._IAttribute> _attributes;
    public readonly RAST._IVisibility _pub;
    public readonly RAST._IFn _fun;
    public ImplMember_FnDecl(Dafny.ISequence<Dafny.Rune> docString, Dafny.ISequence<RAST._IAttribute> attributes, RAST._IVisibility pub, RAST._IFn fun) : base() {
      this._docString = docString;
      this._attributes = attributes;
      this._pub = pub;
      this._fun = fun;
    }
    public override _IImplMember DowncastClone() {
      if (this is _IImplMember dt) { return dt; }
      return new ImplMember_FnDecl(_docString, _attributes, _pub, _fun);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ImplMember_FnDecl;
      return oth != null && object.Equals(this._docString, oth._docString) && object.Equals(this._attributes, oth._attributes) && object.Equals(this._pub, oth._pub) && object.Equals(this._fun, oth._fun);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._docString));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._attributes));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pub));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fun));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ImplMember.FnDecl";
      s += "(";
      s += this._docString.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._attributes);
      s += ", ";
      s += Dafny.Helpers.ToString(this._pub);
      s += ", ";
      s += Dafny.Helpers.ToString(this._fun);
      s += ")";
      return s;
    }
  }
  public class ImplMember_ImplMemberMacro : ImplMember {
    public readonly RAST._IExpr _expr;
    public ImplMember_ImplMemberMacro(RAST._IExpr expr) : base() {
      this._expr = expr;
    }
    public override _IImplMember DowncastClone() {
      if (this is _IImplMember dt) { return dt; }
      return new ImplMember_ImplMemberMacro(_expr);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.ImplMember_ImplMemberMacro;
      return oth != null && object.Equals(this._expr, oth._expr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.ImplMember.ImplMemberMacro";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ")";
      return s;
    }
  }

  public interface _IVisibility {
    bool is_PUB { get; }
    bool is_PRIV { get; }
    _IVisibility DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString();
  }
  public abstract class Visibility : _IVisibility {
    public Visibility() {
    }
    private static readonly RAST._IVisibility theDefault = create_PUB();
    public static RAST._IVisibility Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IVisibility> _TYPE = new Dafny.TypeDescriptor<RAST._IVisibility>(RAST.Visibility.Default());
    public static Dafny.TypeDescriptor<RAST._IVisibility> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IVisibility create_PUB() {
      return new Visibility_PUB();
    }
    public static _IVisibility create_PRIV() {
      return new Visibility_PRIV();
    }
    public bool is_PUB { get { return this is Visibility_PUB; } }
    public bool is_PRIV { get { return this is Visibility_PRIV; } }
    public static System.Collections.Generic.IEnumerable<_IVisibility> AllSingletonConstructors {
      get {
        yield return Visibility.create_PUB();
        yield return Visibility.create_PRIV();
      }
    }
    public abstract _IVisibility DowncastClone();
    public Dafny.ISequence<Dafny.Rune> _ToString() {
      if ((this).is_PUB) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub ");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      }
    }
  }
  public class Visibility_PUB : Visibility {
    public Visibility_PUB() : base() {
    }
    public override _IVisibility DowncastClone() {
      if (this is _IVisibility dt) { return dt; }
      return new Visibility_PUB();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Visibility_PUB;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Visibility.PUB";
      return s;
    }
  }
  public class Visibility_PRIV : Visibility {
    public Visibility_PRIV() : base() {
    }
    public override _IVisibility DowncastClone() {
      if (this is _IVisibility dt) { return dt; }
      return new Visibility_PRIV();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Visibility_PRIV;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Visibility.PRIV";
      return s;
    }
  }

  public interface _IFormal {
    bool is_Formal { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IType dtor_tpe { get; }
    _IFormal DowncastClone();
    RAST._IFormal Replace(Func<RAST._IType, RAST._IType> ft);
    __T Fold<__T>(__T acc, Func<__T, RAST._IType, __T> ft);
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Formal : _IFormal {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly RAST._IType _tpe;
    public Formal(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe) {
      this._name = name;
      this._tpe = tpe;
    }
    public _IFormal DowncastClone() {
      if (this is _IFormal dt) { return dt; }
      return new Formal(_name, _tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Formal;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._tpe, oth._tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Formal.Formal";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ")";
      return s;
    }
    private static readonly RAST._IFormal theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, RAST.Type.Default());
    public static RAST._IFormal Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IFormal> _TYPE = new Dafny.TypeDescriptor<RAST._IFormal>(RAST.Formal.Default());
    public static Dafny.TypeDescriptor<RAST._IFormal> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IFormal create(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe) {
      return new Formal(name, tpe);
    }
    public static _IFormal create_Formal(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe) {
      return create(name, tpe);
    }
    public bool is_Formal { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        return this._tpe;
      }
    }
    public static RAST._IFormal ImplicitlyTyped(Dafny.ISequence<Dafny.Rune> name) {
      return RAST.Formal.create(name, RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_")));
    }
    public RAST._IFormal Replace(Func<RAST._IType, RAST._IType> ft) {
      return RAST.Formal.create((this).dtor_name, ((this).dtor_tpe).Replace(ft));
    }
    public __T Fold<__T>(__T acc, Func<__T, RAST._IType, __T> ft)
    {
      return ((this).dtor_tpe).Fold<__T>(acc, ft);
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      if ((((this).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) && (object.Equals(((this).dtor_tpe).Expand(), RAST.__default.SelfOwned))) {
        return (this).dtor_name;
      } else if ((((this).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) && (object.Equals((this).dtor_tpe, RAST.__default.SelfBorrowed))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"), (this).dtor_name);
      } else if ((((this).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) && (object.Equals((this).dtor_tpe, RAST.__default.SelfBorrowedMut))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut "), (this).dtor_name);
      } else if ((((this).dtor_tpe).is_TIdentifier) && ((((this).dtor_tpe).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_")))) {
        return (this).dtor_name;
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((this).dtor_tpe)._ToString(ind));
      }
    }
    public static RAST._IFormal selfBorrowed { get {
      return RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), RAST.__default.SelfBorrowed);
    } }
    public static RAST._IFormal selfOwned { get {
      return RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), RAST.__default.SelfOwned);
    } }
    public static RAST._IFormal selfBorrowedMut { get {
      return RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), RAST.__default.SelfBorrowedMut);
    } }
  }

  public interface _IPattern {
    bool is_RawPattern { get; }
    Dafny.ISequence<Dafny.Rune> dtor_content { get; }
  }
  public class Pattern : _IPattern {
    public readonly Dafny.ISequence<Dafny.Rune> _content;
    public Pattern(Dafny.ISequence<Dafny.Rune> content) {
      this._content = content;
    }
    public static Dafny.ISequence<Dafny.Rune> DowncastClone(Dafny.ISequence<Dafny.Rune> _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Pattern;
      return oth != null && object.Equals(this._content, oth._content);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._content));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Pattern.RawPattern";
      s += "(";
      s += this._content.ToVerbatimString(true);
      s += ")";
      return s;
    }
    private static readonly Dafny.ISequence<Dafny.Rune> theDefault = Dafny.Sequence<Dafny.Rune>.Empty;
    public static Dafny.ISequence<Dafny.Rune> Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>>(Dafny.Sequence<Dafny.Rune>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<Dafny.Rune>> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPattern create(Dafny.ISequence<Dafny.Rune> content) {
      return new Pattern(content);
    }
    public static _IPattern create_RawPattern(Dafny.ISequence<Dafny.Rune> content) {
      return create(content);
    }
    public bool is_RawPattern { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_content {
      get {
        return this._content;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> _this, Dafny.ISequence<Dafny.Rune> ind) {
      return (_this);
    }
  }

  public interface _IMatchCase {
    bool is_MatchCase { get; }
    Dafny.ISequence<Dafny.Rune> dtor_pattern { get; }
    RAST._IExpr dtor_rhs { get; }
    _IMatchCase DowncastClone();
    RAST._IMatchCase Replace(Func<RAST._IExpr, RAST._IExpr> mapping, Func<RAST._IType, RAST._IType> mappingType);
    __T Fold<__T>(__T acc, Func<__T, RAST._IExpr, __T> f, Func<__T, RAST._IType, __T> ft);
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class MatchCase : _IMatchCase {
    public readonly Dafny.ISequence<Dafny.Rune> _pattern;
    public readonly RAST._IExpr _rhs;
    public MatchCase(Dafny.ISequence<Dafny.Rune> pattern, RAST._IExpr rhs) {
      this._pattern = pattern;
      this._rhs = rhs;
    }
    public _IMatchCase DowncastClone() {
      if (this is _IMatchCase dt) { return dt; }
      return new MatchCase(_pattern, _rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.MatchCase;
      return oth != null && object.Equals(this._pattern, oth._pattern) && object.Equals(this._rhs, oth._rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pattern));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.MatchCase.MatchCase";
      s += "(";
      s += Dafny.Helpers.ToString(this._pattern);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rhs);
      s += ")";
      return s;
    }
    private static readonly RAST._IMatchCase theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, RAST.Expr.Default());
    public static RAST._IMatchCase Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IMatchCase> _TYPE = new Dafny.TypeDescriptor<RAST._IMatchCase>(RAST.MatchCase.Default());
    public static Dafny.TypeDescriptor<RAST._IMatchCase> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMatchCase create(Dafny.ISequence<Dafny.Rune> pattern, RAST._IExpr rhs) {
      return new MatchCase(pattern, rhs);
    }
    public static _IMatchCase create_MatchCase(Dafny.ISequence<Dafny.Rune> pattern, RAST._IExpr rhs) {
      return create(pattern, rhs);
    }
    public bool is_MatchCase { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_pattern {
      get {
        return this._pattern;
      }
    }
    public RAST._IExpr dtor_rhs {
      get {
        return this._rhs;
      }
    }
    public RAST._IMatchCase Replace(Func<RAST._IExpr, RAST._IExpr> mapping, Func<RAST._IType, RAST._IType> mappingType)
    {
      return RAST.MatchCase.create((this).dtor_pattern, ((this).dtor_rhs).Replace(mapping, mappingType));
    }
    public __T Fold<__T>(__T acc, Func<__T, RAST._IExpr, __T> f, Func<__T, RAST._IType, __T> ft)
    {
      return ((this).dtor_rhs).Fold<__T>(acc, f, ft);
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      Dafny.ISequence<Dafny.Rune> _0_newIndent = ((((this).dtor_rhs).is_Block) ? (ind) : (Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)));
      Dafny.ISequence<Dafny.Rune> _1_rhsString = ((this).dtor_rhs)._ToString(_0_newIndent);
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(RAST.Pattern._ToString((this).dtor_pattern, ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" =>")), ((((_1_rhsString).Contains(new Dafny.Rune('\n'))) && (((_1_rhsString).Select(BigInteger.Zero)) != (new Dafny.Rune('{')))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind), RAST.__default.IND), _1_rhsString)) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), _1_rhsString))));
    }
  }

  public interface _IAssignIdentifier {
    bool is_AssignIdentifier { get; }
    Dafny.ISequence<Dafny.Rune> dtor_identifier { get; }
    RAST._IExpr dtor_rhs { get; }
    _IAssignIdentifier DowncastClone();
    RAST._IAssignIdentifier Replace(Func<RAST._IExpr, RAST._IExpr> f, Func<RAST._IType, RAST._IType> ft);
    __T Fold<__T>(__T acc, Func<__T, RAST._IExpr, __T> f, Func<__T, RAST._IType, __T> ft);
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class AssignIdentifier : _IAssignIdentifier {
    public readonly Dafny.ISequence<Dafny.Rune> _identifier;
    public readonly RAST._IExpr _rhs;
    public AssignIdentifier(Dafny.ISequence<Dafny.Rune> identifier, RAST._IExpr rhs) {
      this._identifier = identifier;
      this._rhs = rhs;
    }
    public _IAssignIdentifier DowncastClone() {
      if (this is _IAssignIdentifier dt) { return dt; }
      return new AssignIdentifier(_identifier, _rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.AssignIdentifier;
      return oth != null && object.Equals(this._identifier, oth._identifier) && object.Equals(this._rhs, oth._rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._identifier));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.AssignIdentifier.AssignIdentifier";
      s += "(";
      s += this._identifier.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rhs);
      s += ")";
      return s;
    }
    private static readonly RAST._IAssignIdentifier theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, RAST.Expr.Default());
    public static RAST._IAssignIdentifier Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IAssignIdentifier> _TYPE = new Dafny.TypeDescriptor<RAST._IAssignIdentifier>(RAST.AssignIdentifier.Default());
    public static Dafny.TypeDescriptor<RAST._IAssignIdentifier> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAssignIdentifier create(Dafny.ISequence<Dafny.Rune> identifier, RAST._IExpr rhs) {
      return new AssignIdentifier(identifier, rhs);
    }
    public static _IAssignIdentifier create_AssignIdentifier(Dafny.ISequence<Dafny.Rune> identifier, RAST._IExpr rhs) {
      return create(identifier, rhs);
    }
    public bool is_AssignIdentifier { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_identifier {
      get {
        return this._identifier;
      }
    }
    public RAST._IExpr dtor_rhs {
      get {
        return this._rhs;
      }
    }
    public RAST._IAssignIdentifier Replace(Func<RAST._IExpr, RAST._IExpr> f, Func<RAST._IType, RAST._IType> ft)
    {
      return RAST.AssignIdentifier.create((this).dtor_identifier, ((this).dtor_rhs).Replace(f, ft));
    }
    public __T Fold<__T>(__T acc, Func<__T, RAST._IExpr, __T> f, Func<__T, RAST._IType, __T> ft)
    {
      return ((this).dtor_rhs).Fold<__T>(acc, f, ft);
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((this).dtor_identifier, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), ((this).dtor_rhs)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)));
    }
  }

  public interface _IDeclareType {
    bool is_MUT { get; }
    bool is_CONST { get; }
    _IDeclareType DowncastClone();
  }
  public abstract class DeclareType : _IDeclareType {
    public DeclareType() {
    }
    private static readonly RAST._IDeclareType theDefault = create_MUT();
    public static RAST._IDeclareType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IDeclareType> _TYPE = new Dafny.TypeDescriptor<RAST._IDeclareType>(RAST.DeclareType.Default());
    public static Dafny.TypeDescriptor<RAST._IDeclareType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeclareType create_MUT() {
      return new DeclareType_MUT();
    }
    public static _IDeclareType create_CONST() {
      return new DeclareType_CONST();
    }
    public bool is_MUT { get { return this is DeclareType_MUT; } }
    public bool is_CONST { get { return this is DeclareType_CONST; } }
    public static System.Collections.Generic.IEnumerable<_IDeclareType> AllSingletonConstructors {
      get {
        yield return DeclareType.create_MUT();
        yield return DeclareType.create_CONST();
      }
    }
    public abstract _IDeclareType DowncastClone();
  }
  public class DeclareType_MUT : DeclareType {
    public DeclareType_MUT() : base() {
    }
    public override _IDeclareType DowncastClone() {
      if (this is _IDeclareType dt) { return dt; }
      return new DeclareType_MUT();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.DeclareType_MUT;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.DeclareType.MUT";
      return s;
    }
  }
  public class DeclareType_CONST : DeclareType {
    public DeclareType_CONST() : base() {
    }
    public override _IDeclareType DowncastClone() {
      if (this is _IDeclareType dt) { return dt; }
      return new DeclareType_CONST();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.DeclareType_CONST;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.DeclareType.CONST";
      return s;
    }
  }

  public interface _IAssociativity {
    bool is_LeftToRight { get; }
    bool is_RightToLeft { get; }
    bool is_RequiresParentheses { get; }
    _IAssociativity DowncastClone();
  }
  public abstract class Associativity : _IAssociativity {
    public Associativity() {
    }
    private static readonly RAST._IAssociativity theDefault = create_LeftToRight();
    public static RAST._IAssociativity Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IAssociativity> _TYPE = new Dafny.TypeDescriptor<RAST._IAssociativity>(RAST.Associativity.Default());
    public static Dafny.TypeDescriptor<RAST._IAssociativity> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAssociativity create_LeftToRight() {
      return new Associativity_LeftToRight();
    }
    public static _IAssociativity create_RightToLeft() {
      return new Associativity_RightToLeft();
    }
    public static _IAssociativity create_RequiresParentheses() {
      return new Associativity_RequiresParentheses();
    }
    public bool is_LeftToRight { get { return this is Associativity_LeftToRight; } }
    public bool is_RightToLeft { get { return this is Associativity_RightToLeft; } }
    public bool is_RequiresParentheses { get { return this is Associativity_RequiresParentheses; } }
    public static System.Collections.Generic.IEnumerable<_IAssociativity> AllSingletonConstructors {
      get {
        yield return Associativity.create_LeftToRight();
        yield return Associativity.create_RightToLeft();
        yield return Associativity.create_RequiresParentheses();
      }
    }
    public abstract _IAssociativity DowncastClone();
  }
  public class Associativity_LeftToRight : Associativity {
    public Associativity_LeftToRight() : base() {
    }
    public override _IAssociativity DowncastClone() {
      if (this is _IAssociativity dt) { return dt; }
      return new Associativity_LeftToRight();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Associativity_LeftToRight;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Associativity.LeftToRight";
      return s;
    }
  }
  public class Associativity_RightToLeft : Associativity {
    public Associativity_RightToLeft() : base() {
    }
    public override _IAssociativity DowncastClone() {
      if (this is _IAssociativity dt) { return dt; }
      return new Associativity_RightToLeft();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Associativity_RightToLeft;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Associativity.RightToLeft";
      return s;
    }
  }
  public class Associativity_RequiresParentheses : Associativity {
    public Associativity_RequiresParentheses() : base() {
    }
    public override _IAssociativity DowncastClone() {
      if (this is _IAssociativity dt) { return dt; }
      return new Associativity_RequiresParentheses();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Associativity_RequiresParentheses;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Associativity.RequiresParentheses";
      return s;
    }
  }

  public interface _IPrintingInfo {
    bool is_UnknownPrecedence { get; }
    bool is_Precedence { get; }
    bool is_SuffixPrecedence { get; }
    bool is_PrecedenceAssociativity { get; }
    BigInteger dtor_precedence { get; }
    RAST._IAssociativity dtor_associativity { get; }
    _IPrintingInfo DowncastClone();
    bool NeedParenthesesFor(RAST._IPrintingInfo underlying);
    bool NeedParenthesesForLeft(RAST._IPrintingInfo underlying);
    bool NeedParenthesesForRight(RAST._IPrintingInfo underlying);
  }
  public abstract class PrintingInfo : _IPrintingInfo {
    public PrintingInfo() {
    }
    private static readonly RAST._IPrintingInfo theDefault = create_UnknownPrecedence();
    public static RAST._IPrintingInfo Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IPrintingInfo> _TYPE = new Dafny.TypeDescriptor<RAST._IPrintingInfo>(RAST.PrintingInfo.Default());
    public static Dafny.TypeDescriptor<RAST._IPrintingInfo> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IPrintingInfo create_UnknownPrecedence() {
      return new PrintingInfo_UnknownPrecedence();
    }
    public static _IPrintingInfo create_Precedence(BigInteger precedence) {
      return new PrintingInfo_Precedence(precedence);
    }
    public static _IPrintingInfo create_SuffixPrecedence(BigInteger precedence) {
      return new PrintingInfo_SuffixPrecedence(precedence);
    }
    public static _IPrintingInfo create_PrecedenceAssociativity(BigInteger precedence, RAST._IAssociativity associativity) {
      return new PrintingInfo_PrecedenceAssociativity(precedence, associativity);
    }
    public bool is_UnknownPrecedence { get { return this is PrintingInfo_UnknownPrecedence; } }
    public bool is_Precedence { get { return this is PrintingInfo_Precedence; } }
    public bool is_SuffixPrecedence { get { return this is PrintingInfo_SuffixPrecedence; } }
    public bool is_PrecedenceAssociativity { get { return this is PrintingInfo_PrecedenceAssociativity; } }
    public BigInteger dtor_precedence {
      get {
        var d = this;
        if (d is PrintingInfo_Precedence) { return ((PrintingInfo_Precedence)d)._precedence; }
        if (d is PrintingInfo_SuffixPrecedence) { return ((PrintingInfo_SuffixPrecedence)d)._precedence; }
        return ((PrintingInfo_PrecedenceAssociativity)d)._precedence;
      }
    }
    public RAST._IAssociativity dtor_associativity {
      get {
        var d = this;
        return ((PrintingInfo_PrecedenceAssociativity)d)._associativity;
      }
    }
    public abstract _IPrintingInfo DowncastClone();
    public bool NeedParenthesesFor(RAST._IPrintingInfo underlying) {
      if ((this).is_UnknownPrecedence) {
        return true;
      } else if ((underlying).is_UnknownPrecedence) {
        return true;
      } else if (((this).dtor_precedence) <= ((underlying).dtor_precedence)) {
        return true;
      } else {
        return false;
      }
    }
    public bool NeedParenthesesForLeft(RAST._IPrintingInfo underlying) {
      if ((this).is_UnknownPrecedence) {
        return true;
      } else if ((underlying).is_UnknownPrecedence) {
        return true;
      } else if (((this).dtor_precedence) <= ((underlying).dtor_precedence)) {
        return ((((this).dtor_precedence) < ((underlying).dtor_precedence)) || (!((this).is_PrecedenceAssociativity))) || (!(((this).dtor_associativity).is_LeftToRight));
      } else {
        return false;
      }
    }
    public bool NeedParenthesesForRight(RAST._IPrintingInfo underlying) {
      if ((this).is_UnknownPrecedence) {
        return true;
      } else if ((underlying).is_UnknownPrecedence) {
        return true;
      } else if (((this).dtor_precedence) <= ((underlying).dtor_precedence)) {
        return ((((this).dtor_precedence) < ((underlying).dtor_precedence)) || (!((this).is_PrecedenceAssociativity))) || (!(((this).dtor_associativity).is_RightToLeft));
      } else {
        return false;
      }
    }
  }
  public class PrintingInfo_UnknownPrecedence : PrintingInfo {
    public PrintingInfo_UnknownPrecedence() : base() {
    }
    public override _IPrintingInfo DowncastClone() {
      if (this is _IPrintingInfo dt) { return dt; }
      return new PrintingInfo_UnknownPrecedence();
    }
    public override bool Equals(object other) {
      var oth = other as RAST.PrintingInfo_UnknownPrecedence;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.PrintingInfo.UnknownPrecedence";
      return s;
    }
  }
  public class PrintingInfo_Precedence : PrintingInfo {
    public readonly BigInteger _precedence;
    public PrintingInfo_Precedence(BigInteger precedence) : base() {
      this._precedence = precedence;
    }
    public override _IPrintingInfo DowncastClone() {
      if (this is _IPrintingInfo dt) { return dt; }
      return new PrintingInfo_Precedence(_precedence);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.PrintingInfo_Precedence;
      return oth != null && this._precedence == oth._precedence;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._precedence));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.PrintingInfo.Precedence";
      s += "(";
      s += Dafny.Helpers.ToString(this._precedence);
      s += ")";
      return s;
    }
  }
  public class PrintingInfo_SuffixPrecedence : PrintingInfo {
    public readonly BigInteger _precedence;
    public PrintingInfo_SuffixPrecedence(BigInteger precedence) : base() {
      this._precedence = precedence;
    }
    public override _IPrintingInfo DowncastClone() {
      if (this is _IPrintingInfo dt) { return dt; }
      return new PrintingInfo_SuffixPrecedence(_precedence);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.PrintingInfo_SuffixPrecedence;
      return oth != null && this._precedence == oth._precedence;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._precedence));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.PrintingInfo.SuffixPrecedence";
      s += "(";
      s += Dafny.Helpers.ToString(this._precedence);
      s += ")";
      return s;
    }
  }
  public class PrintingInfo_PrecedenceAssociativity : PrintingInfo {
    public readonly BigInteger _precedence;
    public readonly RAST._IAssociativity _associativity;
    public PrintingInfo_PrecedenceAssociativity(BigInteger precedence, RAST._IAssociativity associativity) : base() {
      this._precedence = precedence;
      this._associativity = associativity;
    }
    public override _IPrintingInfo DowncastClone() {
      if (this is _IPrintingInfo dt) { return dt; }
      return new PrintingInfo_PrecedenceAssociativity(_precedence, _associativity);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.PrintingInfo_PrecedenceAssociativity;
      return oth != null && this._precedence == oth._precedence && object.Equals(this._associativity, oth._associativity);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._precedence));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._associativity));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.PrintingInfo.PrecedenceAssociativity";
      s += "(";
      s += Dafny.Helpers.ToString(this._precedence);
      s += ", ";
      s += Dafny.Helpers.ToString(this._associativity);
      s += ")";
      return s;
    }
  }

  public interface _IAssignLhs {
    bool is_LocalVar { get; }
    bool is_SelectMember { get; }
    bool is_ExtractTuple { get; }
    bool is_Index { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IExpr dtor_on { get; }
    Dafny.ISequence<Dafny.Rune> dtor_field { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_names { get; }
    RAST._IExpr dtor_expr { get; }
    Dafny.ISequence<RAST._IExpr> dtor_indices { get; }
    _IAssignLhs DowncastClone();
  }
  public abstract class AssignLhs : _IAssignLhs {
    public AssignLhs() {
    }
    private static readonly RAST._IAssignLhs theDefault = create_LocalVar(Dafny.Sequence<Dafny.Rune>.Empty);
    public static RAST._IAssignLhs Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IAssignLhs> _TYPE = new Dafny.TypeDescriptor<RAST._IAssignLhs>(RAST.AssignLhs.Default());
    public static Dafny.TypeDescriptor<RAST._IAssignLhs> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IAssignLhs create_LocalVar(Dafny.ISequence<Dafny.Rune> name) {
      return new AssignLhs_LocalVar(name);
    }
    public static _IAssignLhs create_SelectMember(RAST._IExpr @on, Dafny.ISequence<Dafny.Rune> field) {
      return new AssignLhs_SelectMember(@on, field);
    }
    public static _IAssignLhs create_ExtractTuple(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names) {
      return new AssignLhs_ExtractTuple(names);
    }
    public static _IAssignLhs create_Index(RAST._IExpr expr, Dafny.ISequence<RAST._IExpr> indices) {
      return new AssignLhs_Index(expr, indices);
    }
    public bool is_LocalVar { get { return this is AssignLhs_LocalVar; } }
    public bool is_SelectMember { get { return this is AssignLhs_SelectMember; } }
    public bool is_ExtractTuple { get { return this is AssignLhs_ExtractTuple; } }
    public bool is_Index { get { return this is AssignLhs_Index; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        return ((AssignLhs_LocalVar)d)._name;
      }
    }
    public RAST._IExpr dtor_on {
      get {
        var d = this;
        return ((AssignLhs_SelectMember)d)._on;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_field {
      get {
        var d = this;
        return ((AssignLhs_SelectMember)d)._field;
      }
    }
    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_names {
      get {
        var d = this;
        return ((AssignLhs_ExtractTuple)d)._names;
      }
    }
    public RAST._IExpr dtor_expr {
      get {
        var d = this;
        return ((AssignLhs_Index)d)._expr;
      }
    }
    public Dafny.ISequence<RAST._IExpr> dtor_indices {
      get {
        var d = this;
        return ((AssignLhs_Index)d)._indices;
      }
    }
    public abstract _IAssignLhs DowncastClone();
  }
  public class AssignLhs_LocalVar : AssignLhs {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public AssignLhs_LocalVar(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._name = name;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_LocalVar(_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.AssignLhs_LocalVar;
      return oth != null && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.AssignLhs.LocalVar";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class AssignLhs_SelectMember : AssignLhs {
    public readonly RAST._IExpr _on;
    public readonly Dafny.ISequence<Dafny.Rune> _field;
    public AssignLhs_SelectMember(RAST._IExpr @on, Dafny.ISequence<Dafny.Rune> field) : base() {
      this._on = @on;
      this._field = field;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_SelectMember(_on, _field);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.AssignLhs_SelectMember;
      return oth != null && object.Equals(this._on, oth._on) && object.Equals(this._field, oth._field);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._on));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._field));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.AssignLhs.SelectMember";
      s += "(";
      s += Dafny.Helpers.ToString(this._on);
      s += ", ";
      s += this._field.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class AssignLhs_ExtractTuple : AssignLhs {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _names;
    public AssignLhs_ExtractTuple(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names) : base() {
      this._names = names;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_ExtractTuple(_names);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.AssignLhs_ExtractTuple;
      return oth != null && object.Equals(this._names, oth._names);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._names));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.AssignLhs.ExtractTuple";
      s += "(";
      s += Dafny.Helpers.ToString(this._names);
      s += ")";
      return s;
    }
  }
  public class AssignLhs_Index : AssignLhs {
    public readonly RAST._IExpr _expr;
    public readonly Dafny.ISequence<RAST._IExpr> _indices;
    public AssignLhs_Index(RAST._IExpr expr, Dafny.ISequence<RAST._IExpr> indices) : base() {
      this._expr = expr;
      this._indices = indices;
    }
    public override _IAssignLhs DowncastClone() {
      if (this is _IAssignLhs dt) { return dt; }
      return new AssignLhs_Index(_expr, _indices);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.AssignLhs_Index;
      return oth != null && object.Equals(this._expr, oth._expr) && object.Equals(this._indices, oth._indices);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._indices));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.AssignLhs.Index";
      s += "(";
      s += Dafny.Helpers.ToString(this._expr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._indices);
      s += ")";
      return s;
    }
  }

  public interface _IExpr {
    bool is_RawExpr { get; }
    bool is_ExprFromType { get; }
    bool is_Identifier { get; }
    bool is_Match { get; }
    bool is_StmtExpr { get; }
    bool is_Block { get; }
    bool is_StructBuild { get; }
    bool is_Tuple { get; }
    bool is_UnaryOp { get; }
    bool is_BinaryOp { get; }
    bool is_TypeAscription { get; }
    bool is_TraitCast { get; }
    bool is_LiteralInt { get; }
    bool is_LiteralBool { get; }
    bool is_LiteralString { get; }
    bool is_DeclareVar { get; }
    bool is_Assign { get; }
    bool is_IfExpr { get; }
    bool is_Loop { get; }
    bool is_For { get; }
    bool is_Labelled { get; }
    bool is_Break { get; }
    bool is_Continue { get; }
    bool is_Return { get; }
    bool is_CallType { get; }
    bool is_Call { get; }
    bool is_Select { get; }
    bool is_SelectIndex { get; }
    bool is_ExprFromPath { get; }
    bool is_FunctionSelect { get; }
    bool is_Lambda { get; }
    Dafny.ISequence<Dafny.Rune> dtor_content { get; }
    RAST._IType dtor_tpe { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    RAST._IExpr dtor_matchee { get; }
    Dafny.ISequence<RAST._IMatchCase> dtor_cases { get; }
    RAST._IExpr dtor_stmt { get; }
    RAST._IExpr dtor_rhs { get; }
    RAST._IExpr dtor_underlying { get; }
    Dafny.ISequence<RAST._IAssignIdentifier> dtor_assignments { get; }
    Dafny.ISequence<RAST._IExpr> dtor_arguments { get; }
    Dafny.ISequence<Dafny.Rune> dtor_op1 { get; }
    DAST.Format._IUnaryOpFormat dtor_format { get; }
    Dafny.ISequence<Dafny.Rune> dtor_op2 { get; }
    RAST._IExpr dtor_left { get; }
    RAST._IExpr dtor_right { get; }
    DAST.Format._IBinaryOpFormat dtor_format2 { get; }
    RAST._IType dtor_leftTpe { get; }
    Dafny.ISequence<Dafny.Rune> dtor_value { get; }
    bool dtor_bvalue { get; }
    bool dtor_binary { get; }
    bool dtor_verbatim { get; }
    RAST._IDeclareType dtor_declareType { get; }
    Std.Wrappers._IOption<RAST._IType> dtor_optType { get; }
    Std.Wrappers._IOption<RAST._IExpr> dtor_optRhs { get; }
    Std.Wrappers._IOption<RAST._IAssignLhs> dtor_names { get; }
    RAST._IExpr dtor_cond { get; }
    RAST._IExpr dtor_thn { get; }
    RAST._IExpr dtor_els { get; }
    Std.Wrappers._IOption<RAST._IExpr> dtor_optCond { get; }
    RAST._IExpr dtor_range { get; }
    RAST._IExpr dtor_body { get; }
    Dafny.ISequence<Dafny.Rune> dtor_lbl { get; }
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_optLbl { get; }
    Std.Wrappers._IOption<RAST._IExpr> dtor_optExpr { get; }
    RAST._IExpr dtor_obj { get; }
    Dafny.ISequence<RAST._IType> dtor_typeArguments { get; }
    RAST._IPath dtor_path { get; }
    Dafny.ISequence<RAST._IFormal> dtor_params { get; }
    Std.Wrappers._IOption<RAST._IType> dtor_retType { get; }
    _IExpr DowncastClone();
    RAST._IExpr Replace(Func<RAST._IExpr, RAST._IExpr> f, Func<RAST._IType, RAST._IType> ft);
    __T Fold<__T>(__T acc, Func<__T, RAST._IExpr, __T> f, Func<__T, RAST._IType, __T> ft);
    bool NoExtraSemicolonAfter();
    bool EndsWithTypeThatCanAcceptGenericsWhenPrinting();
    RAST._IPrintingInfo printingInfo { get; }
    bool LeftRequiresParentheses(RAST._IExpr left);
    _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> LeftParentheses(RAST._IExpr left);
    bool RightRequiresParentheses(RAST._IExpr right);
    _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> RightParentheses(RAST._IExpr right);
    Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> RightMostIdentifier();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
    RAST._IExpr And(RAST._IExpr rhs2);
    RAST._IExpr Equals(RAST._IExpr rhs2);
    RAST._IExpr Then(RAST._IExpr rhs2);
    RAST._IExpr Sel(Dafny.ISequence<Dafny.Rune> name);
    RAST._IExpr FSel(Dafny.ISequence<Dafny.Rune> name);
    RAST._IExpr ApplyType(Dafny.ISequence<RAST._IType> typeArguments);
    RAST._IExpr ApplyType1(RAST._IType typeArgument);
    RAST._IExpr Apply(Dafny.ISequence<RAST._IExpr> arguments);
    RAST._IExpr Apply1(RAST._IExpr argument);
    RAST._IExpr Apply0();
    bool IsLhsIdentifier();
    Dafny.ISequence<Dafny.Rune> LhsIdentifierName();
    RAST._IExpr Clone();
    bool IsBorrow();
  }
  public abstract class Expr : _IExpr {
    public Expr() {
    }
    private static readonly RAST._IExpr theDefault = create_RawExpr(Dafny.Sequence<Dafny.Rune>.Empty);
    public static RAST._IExpr Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IExpr> _TYPE = new Dafny.TypeDescriptor<RAST._IExpr>(RAST.Expr.Default());
    public static Dafny.TypeDescriptor<RAST._IExpr> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IExpr create_RawExpr(Dafny.ISequence<Dafny.Rune> content) {
      return new Expr_RawExpr(content);
    }
    public static _IExpr create_ExprFromType(RAST._IType tpe) {
      return new Expr_ExprFromType(tpe);
    }
    public static _IExpr create_Identifier(Dafny.ISequence<Dafny.Rune> name) {
      return new Expr_Identifier(name);
    }
    public static _IExpr create_Match(RAST._IExpr matchee, Dafny.ISequence<RAST._IMatchCase> cases) {
      return new Expr_Match(matchee, cases);
    }
    public static _IExpr create_StmtExpr(RAST._IExpr stmt, RAST._IExpr rhs) {
      return new Expr_StmtExpr(stmt, rhs);
    }
    public static _IExpr create_Block(RAST._IExpr underlying) {
      return new Expr_Block(underlying);
    }
    public static _IExpr create_StructBuild(RAST._IExpr underlying, Dafny.ISequence<RAST._IAssignIdentifier> assignments) {
      return new Expr_StructBuild(underlying, assignments);
    }
    public static _IExpr create_Tuple(Dafny.ISequence<RAST._IExpr> arguments) {
      return new Expr_Tuple(arguments);
    }
    public static _IExpr create_UnaryOp(Dafny.ISequence<Dafny.Rune> op1, RAST._IExpr underlying, DAST.Format._IUnaryOpFormat format) {
      return new Expr_UnaryOp(op1, underlying, format);
    }
    public static _IExpr create_BinaryOp(Dafny.ISequence<Dafny.Rune> op2, RAST._IExpr left, RAST._IExpr right, DAST.Format._IBinaryOpFormat format2) {
      return new Expr_BinaryOp(op2, left, right, format2);
    }
    public static _IExpr create_TypeAscription(RAST._IExpr left, RAST._IType tpe) {
      return new Expr_TypeAscription(left, tpe);
    }
    public static _IExpr create_TraitCast(RAST._IType leftTpe, RAST._IType tpe) {
      return new Expr_TraitCast(leftTpe, tpe);
    }
    public static _IExpr create_LiteralInt(Dafny.ISequence<Dafny.Rune> @value) {
      return new Expr_LiteralInt(@value);
    }
    public static _IExpr create_LiteralBool(bool bvalue) {
      return new Expr_LiteralBool(bvalue);
    }
    public static _IExpr create_LiteralString(Dafny.ISequence<Dafny.Rune> @value, bool binary, bool verbatim) {
      return new Expr_LiteralString(@value, binary, verbatim);
    }
    public static _IExpr create_DeclareVar(RAST._IDeclareType declareType, Dafny.ISequence<Dafny.Rune> name, Std.Wrappers._IOption<RAST._IType> optType, Std.Wrappers._IOption<RAST._IExpr> optRhs) {
      return new Expr_DeclareVar(declareType, name, optType, optRhs);
    }
    public static _IExpr create_Assign(Std.Wrappers._IOption<RAST._IAssignLhs> names, RAST._IExpr rhs) {
      return new Expr_Assign(names, rhs);
    }
    public static _IExpr create_IfExpr(RAST._IExpr cond, RAST._IExpr thn, RAST._IExpr els) {
      return new Expr_IfExpr(cond, thn, els);
    }
    public static _IExpr create_Loop(Std.Wrappers._IOption<RAST._IExpr> optCond, RAST._IExpr underlying) {
      return new Expr_Loop(optCond, underlying);
    }
    public static _IExpr create_For(Dafny.ISequence<Dafny.Rune> name, RAST._IExpr range, RAST._IExpr body) {
      return new Expr_For(name, range, body);
    }
    public static _IExpr create_Labelled(Dafny.ISequence<Dafny.Rune> lbl, RAST._IExpr underlying) {
      return new Expr_Labelled(lbl, underlying);
    }
    public static _IExpr create_Break(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> optLbl) {
      return new Expr_Break(optLbl);
    }
    public static _IExpr create_Continue(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> optLbl) {
      return new Expr_Continue(optLbl);
    }
    public static _IExpr create_Return(Std.Wrappers._IOption<RAST._IExpr> optExpr) {
      return new Expr_Return(optExpr);
    }
    public static _IExpr create_CallType(RAST._IExpr obj, Dafny.ISequence<RAST._IType> typeArguments) {
      return new Expr_CallType(obj, typeArguments);
    }
    public static _IExpr create_Call(RAST._IExpr obj, Dafny.ISequence<RAST._IExpr> arguments) {
      return new Expr_Call(obj, arguments);
    }
    public static _IExpr create_Select(RAST._IExpr obj, Dafny.ISequence<Dafny.Rune> name) {
      return new Expr_Select(obj, name);
    }
    public static _IExpr create_SelectIndex(RAST._IExpr obj, RAST._IExpr range) {
      return new Expr_SelectIndex(obj, range);
    }
    public static _IExpr create_ExprFromPath(RAST._IPath path) {
      return new Expr_ExprFromPath(path);
    }
    public static _IExpr create_FunctionSelect(RAST._IExpr obj, Dafny.ISequence<Dafny.Rune> name) {
      return new Expr_FunctionSelect(obj, name);
    }
    public static _IExpr create_Lambda(Dafny.ISequence<RAST._IFormal> @params, Std.Wrappers._IOption<RAST._IType> retType, RAST._IExpr body) {
      return new Expr_Lambda(@params, retType, body);
    }
    public bool is_RawExpr { get { return this is Expr_RawExpr; } }
    public bool is_ExprFromType { get { return this is Expr_ExprFromType; } }
    public bool is_Identifier { get { return this is Expr_Identifier; } }
    public bool is_Match { get { return this is Expr_Match; } }
    public bool is_StmtExpr { get { return this is Expr_StmtExpr; } }
    public bool is_Block { get { return this is Expr_Block; } }
    public bool is_StructBuild { get { return this is Expr_StructBuild; } }
    public bool is_Tuple { get { return this is Expr_Tuple; } }
    public bool is_UnaryOp { get { return this is Expr_UnaryOp; } }
    public bool is_BinaryOp { get { return this is Expr_BinaryOp; } }
    public bool is_TypeAscription { get { return this is Expr_TypeAscription; } }
    public bool is_TraitCast { get { return this is Expr_TraitCast; } }
    public bool is_LiteralInt { get { return this is Expr_LiteralInt; } }
    public bool is_LiteralBool { get { return this is Expr_LiteralBool; } }
    public bool is_LiteralString { get { return this is Expr_LiteralString; } }
    public bool is_DeclareVar { get { return this is Expr_DeclareVar; } }
    public bool is_Assign { get { return this is Expr_Assign; } }
    public bool is_IfExpr { get { return this is Expr_IfExpr; } }
    public bool is_Loop { get { return this is Expr_Loop; } }
    public bool is_For { get { return this is Expr_For; } }
    public bool is_Labelled { get { return this is Expr_Labelled; } }
    public bool is_Break { get { return this is Expr_Break; } }
    public bool is_Continue { get { return this is Expr_Continue; } }
    public bool is_Return { get { return this is Expr_Return; } }
    public bool is_CallType { get { return this is Expr_CallType; } }
    public bool is_Call { get { return this is Expr_Call; } }
    public bool is_Select { get { return this is Expr_Select; } }
    public bool is_SelectIndex { get { return this is Expr_SelectIndex; } }
    public bool is_ExprFromPath { get { return this is Expr_ExprFromPath; } }
    public bool is_FunctionSelect { get { return this is Expr_FunctionSelect; } }
    public bool is_Lambda { get { return this is Expr_Lambda; } }
    public Dafny.ISequence<Dafny.Rune> dtor_content {
      get {
        var d = this;
        return ((Expr_RawExpr)d)._content;
      }
    }
    public RAST._IType dtor_tpe {
      get {
        var d = this;
        if (d is Expr_ExprFromType) { return ((Expr_ExprFromType)d)._tpe; }
        if (d is Expr_TypeAscription) { return ((Expr_TypeAscription)d)._tpe; }
        return ((Expr_TraitCast)d)._tpe;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        var d = this;
        if (d is Expr_Identifier) { return ((Expr_Identifier)d)._name; }
        if (d is Expr_DeclareVar) { return ((Expr_DeclareVar)d)._name; }
        if (d is Expr_For) { return ((Expr_For)d)._name; }
        if (d is Expr_Select) { return ((Expr_Select)d)._name; }
        return ((Expr_FunctionSelect)d)._name;
      }
    }
    public RAST._IExpr dtor_matchee {
      get {
        var d = this;
        return ((Expr_Match)d)._matchee;
      }
    }
    public Dafny.ISequence<RAST._IMatchCase> dtor_cases {
      get {
        var d = this;
        return ((Expr_Match)d)._cases;
      }
    }
    public RAST._IExpr dtor_stmt {
      get {
        var d = this;
        return ((Expr_StmtExpr)d)._stmt;
      }
    }
    public RAST._IExpr dtor_rhs {
      get {
        var d = this;
        if (d is Expr_StmtExpr) { return ((Expr_StmtExpr)d)._rhs; }
        return ((Expr_Assign)d)._rhs;
      }
    }
    public RAST._IExpr dtor_underlying {
      get {
        var d = this;
        if (d is Expr_Block) { return ((Expr_Block)d)._underlying; }
        if (d is Expr_StructBuild) { return ((Expr_StructBuild)d)._underlying; }
        if (d is Expr_UnaryOp) { return ((Expr_UnaryOp)d)._underlying; }
        if (d is Expr_Loop) { return ((Expr_Loop)d)._underlying; }
        return ((Expr_Labelled)d)._underlying;
      }
    }
    public Dafny.ISequence<RAST._IAssignIdentifier> dtor_assignments {
      get {
        var d = this;
        return ((Expr_StructBuild)d)._assignments;
      }
    }
    public Dafny.ISequence<RAST._IExpr> dtor_arguments {
      get {
        var d = this;
        if (d is Expr_Tuple) { return ((Expr_Tuple)d)._arguments; }
        return ((Expr_Call)d)._arguments;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_op1 {
      get {
        var d = this;
        return ((Expr_UnaryOp)d)._op1;
      }
    }
    public DAST.Format._IUnaryOpFormat dtor_format {
      get {
        var d = this;
        return ((Expr_UnaryOp)d)._format;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_op2 {
      get {
        var d = this;
        return ((Expr_BinaryOp)d)._op2;
      }
    }
    public RAST._IExpr dtor_left {
      get {
        var d = this;
        if (d is Expr_BinaryOp) { return ((Expr_BinaryOp)d)._left; }
        return ((Expr_TypeAscription)d)._left;
      }
    }
    public RAST._IExpr dtor_right {
      get {
        var d = this;
        return ((Expr_BinaryOp)d)._right;
      }
    }
    public DAST.Format._IBinaryOpFormat dtor_format2 {
      get {
        var d = this;
        return ((Expr_BinaryOp)d)._format2;
      }
    }
    public RAST._IType dtor_leftTpe {
      get {
        var d = this;
        return ((Expr_TraitCast)d)._leftTpe;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_value {
      get {
        var d = this;
        if (d is Expr_LiteralInt) { return ((Expr_LiteralInt)d)._value; }
        return ((Expr_LiteralString)d)._value;
      }
    }
    public bool dtor_bvalue {
      get {
        var d = this;
        return ((Expr_LiteralBool)d)._bvalue;
      }
    }
    public bool dtor_binary {
      get {
        var d = this;
        return ((Expr_LiteralString)d)._binary;
      }
    }
    public bool dtor_verbatim {
      get {
        var d = this;
        return ((Expr_LiteralString)d)._verbatim;
      }
    }
    public RAST._IDeclareType dtor_declareType {
      get {
        var d = this;
        return ((Expr_DeclareVar)d)._declareType;
      }
    }
    public Std.Wrappers._IOption<RAST._IType> dtor_optType {
      get {
        var d = this;
        return ((Expr_DeclareVar)d)._optType;
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> dtor_optRhs {
      get {
        var d = this;
        return ((Expr_DeclareVar)d)._optRhs;
      }
    }
    public Std.Wrappers._IOption<RAST._IAssignLhs> dtor_names {
      get {
        var d = this;
        return ((Expr_Assign)d)._names;
      }
    }
    public RAST._IExpr dtor_cond {
      get {
        var d = this;
        return ((Expr_IfExpr)d)._cond;
      }
    }
    public RAST._IExpr dtor_thn {
      get {
        var d = this;
        return ((Expr_IfExpr)d)._thn;
      }
    }
    public RAST._IExpr dtor_els {
      get {
        var d = this;
        return ((Expr_IfExpr)d)._els;
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> dtor_optCond {
      get {
        var d = this;
        return ((Expr_Loop)d)._optCond;
      }
    }
    public RAST._IExpr dtor_range {
      get {
        var d = this;
        if (d is Expr_For) { return ((Expr_For)d)._range; }
        return ((Expr_SelectIndex)d)._range;
      }
    }
    public RAST._IExpr dtor_body {
      get {
        var d = this;
        if (d is Expr_For) { return ((Expr_For)d)._body; }
        return ((Expr_Lambda)d)._body;
      }
    }
    public Dafny.ISequence<Dafny.Rune> dtor_lbl {
      get {
        var d = this;
        return ((Expr_Labelled)d)._lbl;
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> dtor_optLbl {
      get {
        var d = this;
        if (d is Expr_Break) { return ((Expr_Break)d)._optLbl; }
        return ((Expr_Continue)d)._optLbl;
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> dtor_optExpr {
      get {
        var d = this;
        return ((Expr_Return)d)._optExpr;
      }
    }
    public RAST._IExpr dtor_obj {
      get {
        var d = this;
        if (d is Expr_CallType) { return ((Expr_CallType)d)._obj; }
        if (d is Expr_Call) { return ((Expr_Call)d)._obj; }
        if (d is Expr_Select) { return ((Expr_Select)d)._obj; }
        if (d is Expr_SelectIndex) { return ((Expr_SelectIndex)d)._obj; }
        return ((Expr_FunctionSelect)d)._obj;
      }
    }
    public Dafny.ISequence<RAST._IType> dtor_typeArguments {
      get {
        var d = this;
        return ((Expr_CallType)d)._typeArguments;
      }
    }
    public RAST._IPath dtor_path {
      get {
        var d = this;
        return ((Expr_ExprFromPath)d)._path;
      }
    }
    public Dafny.ISequence<RAST._IFormal> dtor_params {
      get {
        var d = this;
        return ((Expr_Lambda)d)._params;
      }
    }
    public Std.Wrappers._IOption<RAST._IType> dtor_retType {
      get {
        var d = this;
        return ((Expr_Lambda)d)._retType;
      }
    }
    public abstract _IExpr DowncastClone();
    public RAST._IExpr Replace(Func<RAST._IExpr, RAST._IExpr> f, Func<RAST._IType, RAST._IType> ft)
    {
      RAST._IExpr _0_r = ((System.Func<RAST._IExpr>)(() => {
        RAST._IExpr _source0 = this;
        {
          if (_source0.is_RawExpr) {
            Dafny.ISequence<Dafny.Rune> _1_content = _source0.dtor_content;
            return this;
          }
        }
        {
          if (_source0.is_ExprFromType) {
            RAST._IType _2_tpe = _source0.dtor_tpe;
            return RAST.Expr.create_ExprFromType((_2_tpe).Replace(ft));
          }
        }
        {
          if (_source0.is_Identifier) {
            Dafny.ISequence<Dafny.Rune> _3_name = _source0.dtor_name;
            return this;
          }
        }
        {
          if (_source0.is_Match) {
            RAST._IExpr _4_matchee = _source0.dtor_matchee;
            Dafny.ISequence<RAST._IMatchCase> _5_cases = _source0.dtor_cases;
            return RAST.Expr.create_Match((_4_matchee).Replace(f, ft), Std.Collections.Seq.__default.Map<RAST._IMatchCase, RAST._IMatchCase>(Dafny.Helpers.Id<Func<Func<RAST._IExpr, RAST._IExpr>, Func<RAST._IType, RAST._IType>, Dafny.ISequence<RAST._IMatchCase>, Func<RAST._IMatchCase, RAST._IMatchCase>>>((_6_f, _7_ft, _8_cases) => ((System.Func<RAST._IMatchCase, RAST._IMatchCase>)((_9_c) => {
  return (_9_c).Replace(_6_f, _7_ft);
})))(f, ft, _5_cases), _5_cases));
          }
        }
        {
          if (_source0.is_StmtExpr) {
            RAST._IExpr _10_stmt = _source0.dtor_stmt;
            RAST._IExpr _11_rhs = _source0.dtor_rhs;
            return RAST.Expr.create_StmtExpr((_10_stmt).Replace(f, ft), (_11_rhs).Replace(f, ft));
          }
        }
        {
          if (_source0.is_Block) {
            RAST._IExpr _12_underlying = _source0.dtor_underlying;
            return RAST.Expr.create_Block((_12_underlying).Replace(f, ft));
          }
        }
        {
          if (_source0.is_StructBuild) {
            RAST._IExpr _13_underlying = _source0.dtor_underlying;
            Dafny.ISequence<RAST._IAssignIdentifier> _14_assignments = _source0.dtor_assignments;
            return RAST.Expr.create_StructBuild((_13_underlying).Replace(f, ft), Std.Collections.Seq.__default.Map<RAST._IAssignIdentifier, RAST._IAssignIdentifier>(Dafny.Helpers.Id<Func<Func<RAST._IExpr, RAST._IExpr>, Func<RAST._IType, RAST._IType>, Dafny.ISequence<RAST._IAssignIdentifier>, Func<RAST._IAssignIdentifier, RAST._IAssignIdentifier>>>((_15_f, _16_ft, _17_assignments) => ((System.Func<RAST._IAssignIdentifier, RAST._IAssignIdentifier>)((_18_a) => {
  return (_18_a).Replace(_15_f, _16_ft);
})))(f, ft, _14_assignments), _14_assignments));
          }
        }
        {
          if (_source0.is_Tuple) {
            Dafny.ISequence<RAST._IExpr> _19_arguments = _source0.dtor_arguments;
            return RAST.Expr.create_Tuple(Std.Collections.Seq.__default.Map<RAST._IExpr, RAST._IExpr>(Dafny.Helpers.Id<Func<Func<RAST._IExpr, RAST._IExpr>, Func<RAST._IType, RAST._IType>, Dafny.ISequence<RAST._IExpr>, Func<RAST._IExpr, RAST._IExpr>>>((_20_f, _21_ft, _22_arguments) => ((System.Func<RAST._IExpr, RAST._IExpr>)((_23_e) => {
  return (_23_e).Replace(_20_f, _21_ft);
})))(f, ft, _19_arguments), _19_arguments));
          }
        }
        {
          if (_source0.is_UnaryOp) {
            Dafny.ISequence<Dafny.Rune> _24_op1 = _source0.dtor_op1;
            RAST._IExpr _25_underlying = _source0.dtor_underlying;
            DAST.Format._IUnaryOpFormat _26_format = _source0.dtor_format;
            return RAST.Expr.create_UnaryOp(_24_op1, (_25_underlying).Replace(f, ft), _26_format);
          }
        }
        {
          if (_source0.is_BinaryOp) {
            Dafny.ISequence<Dafny.Rune> _27_op2 = _source0.dtor_op2;
            RAST._IExpr _28_left = _source0.dtor_left;
            RAST._IExpr _29_right = _source0.dtor_right;
            DAST.Format._IBinaryOpFormat _30_format2 = _source0.dtor_format2;
            return RAST.Expr.create_BinaryOp(_27_op2, (_28_left).Replace(f, ft), (_29_right).Replace(f, ft), _30_format2);
          }
        }
        {
          if (_source0.is_TypeAscription) {
            RAST._IExpr _31_left = _source0.dtor_left;
            RAST._IType _32_tpe = _source0.dtor_tpe;
            return RAST.Expr.create_TypeAscription((_31_left).Replace(f, ft), (_32_tpe).Replace(ft));
          }
        }
        {
          if (_source0.is_TraitCast) {
            RAST._IType _33_leftTpe = _source0.dtor_leftTpe;
            RAST._IType _34_tpe = _source0.dtor_tpe;
            return RAST.Expr.create_TraitCast((_33_leftTpe).Replace(ft), (_34_tpe).Replace(ft));
          }
        }
        {
          if (_source0.is_LiteralInt) {
            Dafny.ISequence<Dafny.Rune> _35_value = _source0.dtor_value;
            return this;
          }
        }
        {
          if (_source0.is_LiteralBool) {
            bool _36_bvalue = _source0.dtor_bvalue;
            return this;
          }
        }
        {
          if (_source0.is_LiteralString) {
            Dafny.ISequence<Dafny.Rune> _37_value = _source0.dtor_value;
            bool _38_binary = _source0.dtor_binary;
            bool _39_verbatim = _source0.dtor_verbatim;
            return this;
          }
        }
        {
          if (_source0.is_DeclareVar) {
            RAST._IDeclareType _40_declareType = _source0.dtor_declareType;
            Dafny.ISequence<Dafny.Rune> _41_name = _source0.dtor_name;
            Std.Wrappers._IOption<RAST._IType> _42_optType = _source0.dtor_optType;
            Std.Wrappers._IOption<RAST._IExpr> _43_optRhs = _source0.dtor_optRhs;
            return RAST.Expr.create_DeclareVar(_40_declareType, _41_name, (((_42_optType).is_None) ? (_42_optType) : (Std.Wrappers.Option<RAST._IType>.create_Some(((_42_optType).dtor_value).Replace(ft)))), (((_43_optRhs).is_None) ? (_43_optRhs) : (Std.Wrappers.Option<RAST._IExpr>.create_Some(((_43_optRhs).dtor_value).Replace(f, ft)))));
          }
        }
        {
          if (_source0.is_Assign) {
            Std.Wrappers._IOption<RAST._IAssignLhs> _44_names = _source0.dtor_names;
            RAST._IExpr _45_rhs = _source0.dtor_rhs;
            return RAST.Expr.create_Assign(_44_names, (_45_rhs).Replace(f, ft));
          }
        }
        {
          if (_source0.is_IfExpr) {
            RAST._IExpr _46_cond = _source0.dtor_cond;
            RAST._IExpr _47_thn = _source0.dtor_thn;
            RAST._IExpr _48_els = _source0.dtor_els;
            return RAST.Expr.create_IfExpr((_46_cond).Replace(f, ft), (_47_thn).Replace(f, ft), (_48_els).Replace(f, ft));
          }
        }
        {
          if (_source0.is_Loop) {
            Std.Wrappers._IOption<RAST._IExpr> _49_optCond = _source0.dtor_optCond;
            RAST._IExpr _50_underlying = _source0.dtor_underlying;
            return RAST.Expr.create_Loop((((_49_optCond).is_None) ? (Std.Wrappers.Option<RAST._IExpr>.create_None()) : (Std.Wrappers.Option<RAST._IExpr>.create_Some(((_49_optCond).dtor_value).Replace(f, ft)))), (_50_underlying).Replace(f, ft));
          }
        }
        {
          if (_source0.is_For) {
            Dafny.ISequence<Dafny.Rune> _51_name = _source0.dtor_name;
            RAST._IExpr _52_range = _source0.dtor_range;
            RAST._IExpr _53_body = _source0.dtor_body;
            return RAST.Expr.create_For(_51_name, (_52_range).Replace(f, ft), (_53_body).Replace(f, ft));
          }
        }
        {
          if (_source0.is_Labelled) {
            Dafny.ISequence<Dafny.Rune> _54_lbl = _source0.dtor_lbl;
            RAST._IExpr _55_underlying = _source0.dtor_underlying;
            return RAST.Expr.create_Labelled(_54_lbl, (_55_underlying).Replace(f, ft));
          }
        }
        {
          if (_source0.is_Break) {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _56_optLbl = _source0.dtor_optLbl;
            return this;
          }
        }
        {
          if (_source0.is_Continue) {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _57_optLbl = _source0.dtor_optLbl;
            return this;
          }
        }
        {
          if (_source0.is_Return) {
            Std.Wrappers._IOption<RAST._IExpr> _58_optExpr = _source0.dtor_optExpr;
            return RAST.Expr.create_Return((((_58_optExpr).is_None) ? (Std.Wrappers.Option<RAST._IExpr>.create_None()) : (Std.Wrappers.Option<RAST._IExpr>.create_Some(((_58_optExpr).dtor_value).Replace(f, ft)))));
          }
        }
        {
          if (_source0.is_CallType) {
            RAST._IExpr _59_obj = _source0.dtor_obj;
            Dafny.ISequence<RAST._IType> _60_typeArguments = _source0.dtor_typeArguments;
            return RAST.Expr.create_CallType((_59_obj).Replace(f, ft), Std.Collections.Seq.__default.Map<RAST._IType, RAST._IType>(Dafny.Helpers.Id<Func<Func<RAST._IType, RAST._IType>, Func<RAST._IType, RAST._IType>>>((_61_ft) => ((System.Func<RAST._IType, RAST._IType>)((_62_tp) => {
  return (_62_tp).Replace(_61_ft);
})))(ft), _60_typeArguments));
          }
        }
        {
          if (_source0.is_Call) {
            RAST._IExpr _63_obj = _source0.dtor_obj;
            Dafny.ISequence<RAST._IExpr> _64_arguments = _source0.dtor_arguments;
            return RAST.Expr.create_Call((_63_obj).Replace(f, ft), Std.Collections.Seq.__default.Map<RAST._IExpr, RAST._IExpr>(Dafny.Helpers.Id<Func<Func<RAST._IExpr, RAST._IExpr>, Func<RAST._IType, RAST._IType>, Func<RAST._IExpr, RAST._IExpr>>>((_65_f, _66_ft) => ((System.Func<RAST._IExpr, RAST._IExpr>)((_67_a) => {
  return (_67_a).Replace(_65_f, _66_ft);
})))(f, ft), _64_arguments));
          }
        }
        {
          if (_source0.is_Select) {
            RAST._IExpr _68_obj = _source0.dtor_obj;
            Dafny.ISequence<Dafny.Rune> _69_name = _source0.dtor_name;
            return RAST.Expr.create_Select((_68_obj).Replace(f, ft), _69_name);
          }
        }
        {
          if (_source0.is_SelectIndex) {
            RAST._IExpr _70_obj = _source0.dtor_obj;
            RAST._IExpr _71_range = _source0.dtor_range;
            return RAST.Expr.create_SelectIndex((_70_obj).Replace(f, ft), (_71_range).Replace(f, ft));
          }
        }
        {
          if (_source0.is_ExprFromPath) {
            RAST._IPath _72_path = _source0.dtor_path;
            return RAST.Expr.create_ExprFromPath(_72_path);
          }
        }
        {
          if (_source0.is_FunctionSelect) {
            RAST._IExpr _73_obj = _source0.dtor_obj;
            Dafny.ISequence<Dafny.Rune> _74_name = _source0.dtor_name;
            return RAST.Expr.create_FunctionSelect((_73_obj).Replace(f, ft), _74_name);
          }
        }
        {
          Dafny.ISequence<RAST._IFormal> _75_params = _source0.dtor_params;
          Std.Wrappers._IOption<RAST._IType> _76_retType = _source0.dtor_retType;
          RAST._IExpr _77_body = _source0.dtor_body;
          return RAST.Expr.create_Lambda(Std.Collections.Seq.__default.Map<RAST._IFormal, RAST._IFormal>(Dafny.Helpers.Id<Func<Func<RAST._IType, RAST._IType>, Func<RAST._IFormal, RAST._IFormal>>>((_78_ft) => ((System.Func<RAST._IFormal, RAST._IFormal>)((_79_f) => {
  return (_79_f).Replace(_78_ft);
})))(ft), _75_params), (((_76_retType).is_None) ? (Std.Wrappers.Option<RAST._IType>.create_None()) : (Std.Wrappers.Option<RAST._IType>.create_Some(((_76_retType).dtor_value).Replace(ft)))), (_77_body).Replace(f, ft));
        }
      }))();
      return Dafny.Helpers.Id<Func<RAST._IExpr, RAST._IExpr>>(f)(_0_r);
    }
    public __T Fold<__T>(__T acc, Func<__T, RAST._IExpr, __T> f, Func<__T, RAST._IType, __T> ft)
    {
      __T _0_acc = Dafny.Helpers.Id<Func<__T, RAST._IExpr, __T>>(f)(acc, this);
      RAST._IExpr _source0 = this;
      {
        if (_source0.is_RawExpr) {
          Dafny.ISequence<Dafny.Rune> _1_content = _source0.dtor_content;
          return _0_acc;
        }
      }
      {
        if (_source0.is_ExprFromType) {
          RAST._IType _2_tpe = _source0.dtor_tpe;
          return (_2_tpe).Fold<__T>(_0_acc, ft);
        }
      }
      {
        if (_source0.is_Identifier) {
          Dafny.ISequence<Dafny.Rune> _3_name = _source0.dtor_name;
          return _0_acc;
        }
      }
      {
        if (_source0.is_Match) {
          RAST._IExpr _4_matchee = _source0.dtor_matchee;
          Dafny.ISequence<RAST._IMatchCase> _5_cases = _source0.dtor_cases;
          __T _6_acc = (_4_matchee).Fold<__T>(_0_acc, f, ft);
          return RAST.__default.FoldLeft<__T, RAST._IMatchCase>(Dafny.Helpers.Id<Func<Func<__T, RAST._IExpr, __T>, Func<__T, RAST._IType, __T>, Dafny.ISequence<RAST._IMatchCase>, Func<__T, RAST._IMatchCase, __T>>>((_7_f, _8_ft, _9_cases) => ((System.Func<__T, RAST._IMatchCase, __T>)((_10_acc, _11_c) => {
            return (_11_c).Fold<__T>(_10_acc, _7_f, _8_ft);
          })))(f, ft, _5_cases), _6_acc, _5_cases);
        }
      }
      {
        if (_source0.is_StmtExpr) {
          RAST._IExpr _12_stmt = _source0.dtor_stmt;
          RAST._IExpr _13_rhs = _source0.dtor_rhs;
          return (_13_rhs).Fold<__T>((_12_stmt).Fold<__T>(_0_acc, f, ft), f, ft);
        }
      }
      {
        if (_source0.is_Block) {
          RAST._IExpr _14_underlying = _source0.dtor_underlying;
          return (_14_underlying).Fold<__T>(_0_acc, f, ft);
        }
      }
      {
        if (_source0.is_StructBuild) {
          RAST._IExpr _15_underlying = _source0.dtor_underlying;
          Dafny.ISequence<RAST._IAssignIdentifier> _16_assignments = _source0.dtor_assignments;
          return RAST.__default.FoldLeft<__T, RAST._IAssignIdentifier>(Dafny.Helpers.Id<Func<Func<__T, RAST._IExpr, __T>, Func<__T, RAST._IType, __T>, Dafny.ISequence<RAST._IAssignIdentifier>, Func<__T, RAST._IAssignIdentifier, __T>>>((_17_f, _18_ft, _19_assignments) => ((System.Func<__T, RAST._IAssignIdentifier, __T>)((_20_acc, _21_c) => {
            return (_21_c).Fold<__T>(_20_acc, _17_f, _18_ft);
          })))(f, ft, _16_assignments), (_15_underlying).Fold<__T>(_0_acc, f, ft), _16_assignments);
        }
      }
      {
        if (_source0.is_Tuple) {
          Dafny.ISequence<RAST._IExpr> _22_arguments = _source0.dtor_arguments;
          return RAST.__default.FoldLeft<__T, RAST._IExpr>(Dafny.Helpers.Id<Func<Func<__T, RAST._IExpr, __T>, Func<__T, RAST._IType, __T>, Dafny.ISequence<RAST._IExpr>, Func<__T, RAST._IExpr, __T>>>((_23_f, _24_ft, _25_arguments) => ((System.Func<__T, RAST._IExpr, __T>)((_26_acc, _27_e) => {
            return (_27_e).Fold<__T>(_26_acc, _23_f, _24_ft);
          })))(f, ft, _22_arguments), _0_acc, _22_arguments);
        }
      }
      {
        if (_source0.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> _28_op1 = _source0.dtor_op1;
          RAST._IExpr _29_underlying = _source0.dtor_underlying;
          DAST.Format._IUnaryOpFormat _30_format = _source0.dtor_format;
          return (_29_underlying).Fold<__T>(_0_acc, f, ft);
        }
      }
      {
        if (_source0.is_BinaryOp) {
          Dafny.ISequence<Dafny.Rune> _31_op2 = _source0.dtor_op2;
          RAST._IExpr _32_left = _source0.dtor_left;
          RAST._IExpr _33_right = _source0.dtor_right;
          DAST.Format._IBinaryOpFormat _34_format2 = _source0.dtor_format2;
          return (_33_right).Fold<__T>((_32_left).Fold<__T>(_0_acc, f, ft), f, ft);
        }
      }
      {
        if (_source0.is_TypeAscription) {
          RAST._IExpr _35_left = _source0.dtor_left;
          RAST._IType _36_tpe = _source0.dtor_tpe;
          return (_36_tpe).Fold<__T>((_35_left).Fold<__T>(_0_acc, f, ft), ft);
        }
      }
      {
        if (_source0.is_TraitCast) {
          RAST._IType _37_leftTpe = _source0.dtor_leftTpe;
          RAST._IType _38_tpe = _source0.dtor_tpe;
          return (_38_tpe).Fold<__T>((_37_leftTpe).Fold<__T>(_0_acc, ft), ft);
        }
      }
      {
        if (_source0.is_LiteralInt) {
          Dafny.ISequence<Dafny.Rune> _39_value = _source0.dtor_value;
          return _0_acc;
        }
      }
      {
        if (_source0.is_LiteralBool) {
          bool _40_bvalue = _source0.dtor_bvalue;
          return _0_acc;
        }
      }
      {
        if (_source0.is_LiteralString) {
          Dafny.ISequence<Dafny.Rune> _41_value = _source0.dtor_value;
          bool _42_binary = _source0.dtor_binary;
          bool _43_verbatim = _source0.dtor_verbatim;
          return _0_acc;
        }
      }
      {
        if (_source0.is_DeclareVar) {
          RAST._IDeclareType _44_declareType = _source0.dtor_declareType;
          Dafny.ISequence<Dafny.Rune> _45_name = _source0.dtor_name;
          Std.Wrappers._IOption<RAST._IType> _46_optType = _source0.dtor_optType;
          Std.Wrappers._IOption<RAST._IExpr> _47_optRhs = _source0.dtor_optRhs;
          __T _48_acc = (((_46_optType).is_None) ? (_0_acc) : (((_46_optType).dtor_value).Fold<__T>(_0_acc, ft)));
          if ((_47_optRhs).is_None) {
            return _48_acc;
          } else {
            return ((_47_optRhs).dtor_value).Fold<__T>(_48_acc, f, ft);
          }
        }
      }
      {
        if (_source0.is_Assign) {
          Std.Wrappers._IOption<RAST._IAssignLhs> _49_names = _source0.dtor_names;
          RAST._IExpr _50_rhs = _source0.dtor_rhs;
          return (_50_rhs).Fold<__T>(_0_acc, f, ft);
        }
      }
      {
        if (_source0.is_IfExpr) {
          RAST._IExpr _51_cond = _source0.dtor_cond;
          RAST._IExpr _52_thn = _source0.dtor_thn;
          RAST._IExpr _53_els = _source0.dtor_els;
          __T _54_acc = (_51_cond).Fold<__T>(_0_acc, f, ft);
          __T _55_acc = (_52_thn).Fold<__T>(_54_acc, f, ft);
          return (_53_els).Fold<__T>(_55_acc, f, ft);
        }
      }
      {
        if (_source0.is_Loop) {
          Std.Wrappers._IOption<RAST._IExpr> _56_optCond = _source0.dtor_optCond;
          RAST._IExpr _57_underlying = _source0.dtor_underlying;
          __T _58_acc = (((_56_optCond).is_None) ? (_0_acc) : (((_56_optCond).dtor_value).Fold<__T>(_0_acc, f, ft)));
          return (_57_underlying).Fold<__T>(_58_acc, f, ft);
        }
      }
      {
        if (_source0.is_For) {
          Dafny.ISequence<Dafny.Rune> _59_name = _source0.dtor_name;
          RAST._IExpr _60_range = _source0.dtor_range;
          RAST._IExpr _61_body = _source0.dtor_body;
          __T _62_acc = (_60_range).Fold<__T>(_0_acc, f, ft);
          return (_61_body).Fold<__T>(_62_acc, f, ft);
        }
      }
      {
        if (_source0.is_Labelled) {
          Dafny.ISequence<Dafny.Rune> _63_lbl = _source0.dtor_lbl;
          RAST._IExpr _64_underlying = _source0.dtor_underlying;
          return (_64_underlying).Fold<__T>(_0_acc, f, ft);
        }
      }
      {
        if (_source0.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _65_optLbl = _source0.dtor_optLbl;
          return _0_acc;
        }
      }
      {
        if (_source0.is_Continue) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _66_optLbl = _source0.dtor_optLbl;
          return _0_acc;
        }
      }
      {
        if (_source0.is_Return) {
          Std.Wrappers._IOption<RAST._IExpr> _67_optExpr = _source0.dtor_optExpr;
          if ((_67_optExpr).is_None) {
            return _0_acc;
          } else {
            return ((_67_optExpr).dtor_value).Fold<__T>(_0_acc, f, ft);
          }
        }
      }
      {
        if (_source0.is_CallType) {
          RAST._IExpr _68_obj = _source0.dtor_obj;
          Dafny.ISequence<RAST._IType> _69_typeArguments = _source0.dtor_typeArguments;
          __T _70_acc = (_68_obj).Fold<__T>(_0_acc, f, ft);
          return RAST.__default.FoldLeft<__T, RAST._IType>(Dafny.Helpers.Id<Func<Func<__T, RAST._IType, __T>, Dafny.ISequence<RAST._IType>, Func<__T, RAST._IType, __T>>>((_71_ft, _72_typeArguments) => ((System.Func<__T, RAST._IType, __T>)((_73_acc, _74_t) => {
            return (_74_t).Fold<__T>(_73_acc, _71_ft);
          })))(ft, _69_typeArguments), _70_acc, _69_typeArguments);
        }
      }
      {
        if (_source0.is_Call) {
          RAST._IExpr _75_obj = _source0.dtor_obj;
          Dafny.ISequence<RAST._IExpr> _76_arguments = _source0.dtor_arguments;
          __T _77_acc = (_75_obj).Fold<__T>(_0_acc, f, ft);
          return RAST.__default.FoldLeft<__T, RAST._IExpr>(Dafny.Helpers.Id<Func<Func<__T, RAST._IExpr, __T>, Func<__T, RAST._IType, __T>, Dafny.ISequence<RAST._IExpr>, Func<__T, RAST._IExpr, __T>>>((_78_f, _79_ft, _80_arguments) => ((System.Func<__T, RAST._IExpr, __T>)((_81_acc, _82_e) => {
            return (_82_e).Fold<__T>(_81_acc, _78_f, _79_ft);
          })))(f, ft, _76_arguments), _77_acc, _76_arguments);
        }
      }
      {
        if (_source0.is_Select) {
          RAST._IExpr _83_obj = _source0.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _84_name = _source0.dtor_name;
          return (_83_obj).Fold<__T>(_0_acc, f, ft);
        }
      }
      {
        if (_source0.is_SelectIndex) {
          RAST._IExpr _85_obj = _source0.dtor_obj;
          RAST._IExpr _86_range = _source0.dtor_range;
          return (_86_range).Fold<__T>((_85_obj).Fold<__T>(_0_acc, f, ft), f, ft);
        }
      }
      {
        if (_source0.is_ExprFromPath) {
          RAST._IPath _87_path = _source0.dtor_path;
          return _0_acc;
        }
      }
      {
        if (_source0.is_FunctionSelect) {
          RAST._IExpr _88_obj = _source0.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _89_name = _source0.dtor_name;
          return (_88_obj).Fold<__T>(_0_acc, f, ft);
        }
      }
      {
        Dafny.ISequence<RAST._IFormal> _90_params = _source0.dtor_params;
        Std.Wrappers._IOption<RAST._IType> _91_retType = _source0.dtor_retType;
        RAST._IExpr _92_body = _source0.dtor_body;
        __T _93_acc = RAST.__default.FoldLeft<__T, RAST._IFormal>(Dafny.Helpers.Id<Func<Func<__T, RAST._IType, __T>, Dafny.ISequence<RAST._IFormal>, Func<__T, RAST._IFormal, __T>>>((_94_ft, _95_params) => ((System.Func<__T, RAST._IFormal, __T>)((_96_acc, _97_param) => {
          return (_97_param).Fold<__T>(_96_acc, _94_ft);
        })))(ft, _90_params), _0_acc, _90_params);
        __T _98_acc = (((_91_retType).is_None) ? (_93_acc) : (((_91_retType).dtor_value).Fold<__T>(_93_acc, ft)));
        return (_92_body).Fold<__T>(_98_acc, f, ft);
      }
    }
    public bool NoExtraSemicolonAfter() {
      return (((((((this).is_DeclareVar) || ((this).is_Assign)) || ((this).is_Break)) || ((this).is_Continue)) || ((this).is_Return)) || ((this).is_For)) || ((((this).is_RawExpr) && ((new BigInteger(((this).dtor_content).Count)).Sign == 1)) && ((((this).dtor_content).Select((new BigInteger(((this).dtor_content).Count)) - (BigInteger.One))) == (new Dafny.Rune(';'))));
    }
    public bool EndsWithTypeThatCanAcceptGenericsWhenPrinting() {
      _IExpr _this = this;
    TAIL_CALL_START: ;
      RAST._IExpr _source0 = _this;
      {
        if (_source0.is_TypeAscription) {
          RAST._IExpr _0_e = _source0.dtor_left;
          RAST._IType _1_tpe = _source0.dtor_tpe;
          return (_1_tpe).EndsWithNameThatCanAcceptGenerics();
        }
      }
      {
        if (_source0.is_BinaryOp) {
          Dafny.ISequence<Dafny.Rune> _2_op2 = _source0.dtor_op2;
          RAST._IExpr _3_left = _source0.dtor_left;
          RAST._IExpr _4_right = _source0.dtor_right;
          DAST.Format._IBinaryOpFormat _5_format = _source0.dtor_format2;
          RAST._IExpr _in0 = _4_right;
          _this = _in0;
          ;
          goto TAIL_CALL_START;
        }
      }
      {
        return false;
      }
    }
    public bool LeftRequiresParentheses(RAST._IExpr left) {
      return ((this).printingInfo).NeedParenthesesForLeft((left).printingInfo);
    }
    public _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> LeftParentheses(RAST._IExpr left) {
      if ((this).LeftRequiresParentheses(left)) {
        return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      } else {
        return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      }
    }
    public bool RightRequiresParentheses(RAST._IExpr right) {
      return ((this).printingInfo).NeedParenthesesForRight((right).printingInfo);
    }
    public _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> RightParentheses(RAST._IExpr right) {
      if ((this).RightRequiresParentheses(right)) {
        return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
      } else {
        return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> RightMostIdentifier() {
      RAST._IExpr _source0 = this;
      {
        if (_source0.is_FunctionSelect) {
          Dafny.ISequence<Dafny.Rune> _0_id = _source0.dtor_name;
          return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_0_id);
        }
      }
      {
        if (_source0.is_ExprFromPath) {
          RAST._IPath _1_p = _source0.dtor_path;
          return (_1_p).RightMostIdentifier();
        }
      }
      {
        if (_source0.is_Identifier) {
          Dafny.ISequence<Dafny.Rune> _2_id = _source0.dtor_name;
          return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2_id);
        }
      }
      {
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      }
    }
    public static Dafny.ISequence<Dafny.Rune> MaxHashes(Dafny.ISequence<Dafny.Rune> s, Dafny.ISequence<Dafny.Rune> currentHashes, Dafny.ISequence<Dafny.Rune> mostHashes)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        if ((new BigInteger((currentHashes).Count)) < (new BigInteger((mostHashes).Count))) {
          return mostHashes;
        } else {
          return currentHashes;
        }
      } else if (((s).Subsequence(BigInteger.Zero, BigInteger.One)).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#"))) {
        Dafny.ISequence<Dafny.Rune> _in0 = (s).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in1 = Dafny.Sequence<Dafny.Rune>.Concat(currentHashes, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#"));
        Dafny.ISequence<Dafny.Rune> _in2 = mostHashes;
        s = _in0;
        currentHashes = _in1;
        mostHashes = _in2;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<Dafny.Rune> _in3 = (s).Drop(BigInteger.One);
        Dafny.ISequence<Dafny.Rune> _in4 = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        Dafny.ISequence<Dafny.Rune> _in5 = (((new BigInteger((currentHashes).Count)) < (new BigInteger((mostHashes).Count))) ? (mostHashes) : (currentHashes));
        s = _in3;
        currentHashes = _in4;
        mostHashes = _in5;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> RemoveDoubleQuotes(Dafny.ISequence<Dafny.Rune> s) {
      Dafny.ISequence<Dafny.Rune> _0___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)) <= (BigInteger.One)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, s);
      } else if (((s).Subsequence(BigInteger.Zero, new BigInteger(2))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@""""""))) {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(@""""));
        Dafny.ISequence<Dafny.Rune> _in0 = (s).Drop(new BigInteger(2));
        s = _in0;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, (s).Subsequence(BigInteger.Zero, BigInteger.One));
        Dafny.ISequence<Dafny.Rune> _in1 = (s).Drop(BigInteger.One);
        s = _in1;
        goto TAIL_CALL_START;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      RAST._IExpr _source0 = this;
      {
        if (_source0.is_Identifier) {
          Dafny.ISequence<Dafny.Rune> _0_name = _source0.dtor_name;
          return _0_name;
        }
      }
      {
        if (_source0.is_ExprFromType) {
          RAST._IType _1_t = _source0.dtor_tpe;
          return (_1_t)._ToString(ind);
        }
      }
      {
        if (_source0.is_LiteralInt) {
          Dafny.ISequence<Dafny.Rune> _2_number = _source0.dtor_value;
          return _2_number;
        }
      }
      {
        if (_source0.is_LiteralBool) {
          bool _3_b = _source0.dtor_bvalue;
          if (_3_b) {
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true");
          } else {
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false");
          }
        }
      }
      {
        if (_source0.is_LiteralString) {
          Dafny.ISequence<Dafny.Rune> _4_characters = _source0.dtor_value;
          bool _5_binary = _source0.dtor_binary;
          bool _6_verbatim = _source0.dtor_verbatim;
          Dafny.ISequence<Dafny.Rune> _7_hashes = ((_6_verbatim) ? (Dafny.Sequence<Dafny.Rune>.Concat(RAST.Expr.MaxHashes(_4_characters, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#"))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((_5_binary) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("b")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), ((_6_verbatim) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r"), _7_hashes)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\"")), ((_6_verbatim) ? (RAST.Expr.RemoveDoubleQuotes(_4_characters)) : (_4_characters))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\"")), _7_hashes);
        }
      }
      {
        if (_source0.is_Match) {
          RAST._IExpr _8_matchee = _source0.dtor_matchee;
          Dafny.ISequence<RAST._IMatchCase> _9_cases = _source0.dtor_cases;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match "), (_8_matchee)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IMatchCase>(_9_cases, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<RAST._IMatchCase>, Func<RAST._IMatchCase, Dafny.ISequence<Dafny.Rune>>>>((_10_ind, _11_cases) => ((System.Func<RAST._IMatchCase, Dafny.ISequence<Dafny.Rune>>)((_12_c) => {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _10_ind), RAST.__default.IND), (_12_c)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_10_ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","));
          })))(ind, _9_cases), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      {
        if (_source0.is_StmtExpr) {
          RAST._IExpr _13_stmt = _source0.dtor_stmt;
          RAST._IExpr _14_rhs = _source0.dtor_rhs;
          if (((_13_stmt).is_RawExpr) && (((_13_stmt).dtor_content).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))) {
            return (_14_rhs)._ToString(ind);
          } else {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_13_stmt)._ToString(ind), (((_13_stmt).NoExtraSemicolonAfter()) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), (_14_rhs)._ToString(ind));
          }
        }
      }
      {
        if (_source0.is_Block) {
          RAST._IExpr _15_underlying = _source0.dtor_underlying;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n"), ind), RAST.__default.IND), (_15_underlying)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      {
        if (_source0.is_IfExpr) {
          RAST._IExpr _16_cond = _source0.dtor_cond;
          RAST._IExpr _17_thn = _source0.dtor_thn;
          RAST._IExpr _18_els = _source0.dtor_els;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if "), (_16_cond)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), ind), RAST.__default.IND), (_17_thn)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")), ((object.Equals(_18_els, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" else {\n"), ind), RAST.__default.IND), (_18_els)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        }
      }
      {
        if (_source0.is_StructBuild) {
          RAST._IExpr _19_name = _source0.dtor_underlying;
          Dafny.ISequence<RAST._IAssignIdentifier> _20_assignments = _source0.dtor_assignments;
          if (((new BigInteger((_20_assignments).Count)).Sign == 1) && ((((_20_assignments).Select(BigInteger.Zero)).dtor_identifier).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_19_name)._ToString(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" (")), RAST.__default.SeqToString<RAST._IAssignIdentifier>(_20_assignments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<RAST._IAssignIdentifier>, Func<RAST._IAssignIdentifier, Dafny.ISequence<Dafny.Rune>>>>((_21_ind, _22_assignments) => ((System.Func<RAST._IAssignIdentifier, Dafny.ISequence<Dafny.Rune>>)((_23_assignment) => {
              return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _21_ind), RAST.__default.IND), ((_23_assignment).dtor_rhs)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_21_ind, RAST.__default.IND)));
            })))(ind, _20_assignments), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), (((new BigInteger((_20_assignments).Count)) > (BigInteger.One)) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
          } else {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_19_name)._ToString(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {")), RAST.__default.SeqToString<RAST._IAssignIdentifier>(_20_assignments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<RAST._IAssignIdentifier>, Func<RAST._IAssignIdentifier, Dafny.ISequence<Dafny.Rune>>>>((_24_ind, _25_assignments) => ((System.Func<RAST._IAssignIdentifier, Dafny.ISequence<Dafny.Rune>>)((_26_assignment) => {
              return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _24_ind), RAST.__default.IND), (_26_assignment)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_24_ind, RAST.__default.IND)));
            })))(ind, _20_assignments), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), (((new BigInteger((_20_assignments).Count)).Sign == 1) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
          }
        }
      }
      {
        if (_source0.is_Tuple) {
          Dafny.ISequence<RAST._IExpr> _27_arguments = _source0.dtor_arguments;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<RAST._IExpr>(_27_arguments, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<RAST._IExpr>, Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>>>((_28_ind, _29_arguments) => ((System.Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>)((_30_arg) => {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), _28_ind), RAST.__default.IND), (_30_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_28_ind, RAST.__default.IND)));
          })))(ind, _27_arguments), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), (((new BigInteger((_27_arguments).Count)).Sign == 1) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"), ind)) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        }
      }
      {
        if (_source0.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> _31_op = _source0.dtor_op1;
          RAST._IExpr _32_underlying = _source0.dtor_underlying;
          DAST.Format._IUnaryOpFormat _33_format = _source0.dtor_format;
          bool _34_isPattern = ((new BigInteger((_31_op).Count)) >= (BigInteger.One)) && (((_31_op).Subsequence(BigInteger.Zero, BigInteger.One)).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")));
          bool _35_isUnsafe = (_31_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe"));
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs0 = ((((!(_34_isPattern)) && (!(_35_isUnsafe))) && (((this).printingInfo).NeedParenthesesFor((_32_underlying).printingInfo))) ? (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))) : (_System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))));
          Dafny.ISequence<Dafny.Rune> _36_leftP = _let_tmp_rhs0.dtor__0;
          Dafny.ISequence<Dafny.Rune> _37_rightP = _let_tmp_rhs0.dtor__1;
          bool _38_opToRight = (((_31_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"))) || (((new BigInteger((_31_op).Count)) >= (new BigInteger(2))) && (((_31_op).Subsequence(BigInteger.Zero, new BigInteger(2))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/*"))))) || (_34_isPattern);
          Dafny.ISequence<Dafny.Rune> _39_leftOp = ((_38_opToRight) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (_31_op));
          Dafny.ISequence<Dafny.Rune> _40_leftOp = (((((_31_op).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut"))) || (_35_isUnsafe)) && (!(_36_leftP).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")))) ? (Dafny.Sequence<Dafny.Rune>.Concat(_39_leftOp, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "))) : (_39_leftOp));
          Dafny.ISequence<Dafny.Rune> _41_rightOp = ((_38_opToRight) ? (_31_op) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_40_leftOp, _36_leftP), (_32_underlying)._ToString(ind)), _37_rightP), _41_rightOp);
        }
      }
      {
        if (_source0.is_TypeAscription) {
          RAST._IExpr _42_left = _source0.dtor_left;
          RAST._IType _43_tpe = _source0.dtor_tpe;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs1 = (this).LeftParentheses(_42_left);
          Dafny.ISequence<Dafny.Rune> _44_leftLeftP = _let_tmp_rhs1.dtor__0;
          Dafny.ISequence<Dafny.Rune> _45_leftRightP = _let_tmp_rhs1.dtor__1;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_44_leftLeftP, (_42_left)._ToString(RAST.__default.IND)), _45_leftRightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ")), (_43_tpe)._ToString(RAST.__default.IND));
        }
      }
      {
        if (_source0.is_TraitCast) {
          RAST._IType _46_leftTpe = _source0.dtor_leftTpe;
          RAST._IType _47_tpe = _source0.dtor_tpe;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_46_leftTpe)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ")), (_47_tpe)._ToString(RAST.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
        }
      }
      {
        if (_source0.is_BinaryOp) {
          Dafny.ISequence<Dafny.Rune> _48_op2 = _source0.dtor_op2;
          RAST._IExpr _49_left = _source0.dtor_left;
          RAST._IExpr _50_right = _source0.dtor_right;
          DAST.Format._IBinaryOpFormat _51_format = _source0.dtor_format2;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs2 = (this).LeftParentheses(_49_left);
          Dafny.ISequence<Dafny.Rune> _52_leftLeftP = _let_tmp_rhs2.dtor__0;
          Dafny.ISequence<Dafny.Rune> _53_leftRighP = _let_tmp_rhs2.dtor__1;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs3 = (this).RightParentheses(_50_right);
          Dafny.ISequence<Dafny.Rune> _54_rightLeftP = _let_tmp_rhs3.dtor__0;
          Dafny.ISequence<Dafny.Rune> _55_rightRightP = _let_tmp_rhs3.dtor__1;
          Dafny.ISequence<Dafny.Rune> _56_opRendered = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), _48_op2), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "));
          Dafny.ISequence<Dafny.Rune> _57_indLeft = (((_52_leftLeftP).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("))) ? (Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)) : (ind));
          Dafny.ISequence<Dafny.Rune> _58_indRight = (((_54_rightLeftP).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("))) ? (Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)) : (ind));
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_52_leftLeftP, (_49_left)._ToString(_57_indLeft)), _53_leftRighP), _56_opRendered), _54_rightLeftP), (_50_right)._ToString(_58_indRight)), _55_rightRightP);
        }
      }
      {
        if (_source0.is_DeclareVar) {
          RAST._IDeclareType _59_declareType = _source0.dtor_declareType;
          Dafny.ISequence<Dafny.Rune> _60_name = _source0.dtor_name;
          Std.Wrappers._IOption<RAST._IType> _61_optType = _source0.dtor_optType;
          Std.Wrappers._IOption<RAST._IExpr> _62_optExpr = _source0.dtor_optRhs;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let "), ((object.Equals(_59_declareType, RAST.DeclareType.create_MUT())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mut ")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), _60_name), (((_61_optType).is_Some) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": "), ((_61_optType).dtor_value)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), (((_62_optExpr).is_Some) ? (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((_62_optExpr).dtor_value)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)), _pat_let67_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(_pat_let67_0, _63_optExprString => (((_63_optExprString).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("= /*issue with empty RHS*/"), ((((_62_optExpr).dtor_value).is_RawExpr) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Empty Raw expr")) : (((((_62_optExpr).dtor_value).is_LiteralString) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Empty string literal")) : (((((_62_optExpr).dtor_value).is_LiteralInt) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Empty int literal")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Another case"))))))))) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "), _63_optExprString)))))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      }
      {
        if (_source0.is_Assign) {
          Std.Wrappers._IOption<RAST._IAssignLhs> _64_names = _source0.dtor_names;
          RAST._IExpr _65_expr = _source0.dtor_rhs;
          Dafny.ISequence<Dafny.Rune> _66_lhs = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
            Std.Wrappers._IOption<RAST._IAssignLhs> _source1 = _64_names;
            {
              if (_source1.is_Some) {
                RAST._IAssignLhs value0 = _source1.dtor_value;
                if (value0.is_LocalVar) {
                  Dafny.ISequence<Dafny.Rune> _67_name = value0.dtor_name;
                  return Dafny.Sequence<Dafny.Rune>.Concat(_67_name, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "));
                }
              }
            }
            {
              if (_source1.is_Some) {
                RAST._IAssignLhs value1 = _source1.dtor_value;
                if (value1.is_SelectMember) {
                  RAST._IExpr _68_member = value1.dtor_on;
                  Dafny.ISequence<Dafny.Rune> _69_field = value1.dtor_field;
                  _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs4 = (RAST.Expr.create_Select(_68_member, _69_field)).LeftParentheses(_68_member);
                  Dafny.ISequence<Dafny.Rune> _70_leftP = _let_tmp_rhs4.dtor__0;
                  Dafny.ISequence<Dafny.Rune> _71_rightP = _let_tmp_rhs4.dtor__1;
                  return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_70_leftP, (_68_member)._ToString(ind)), _71_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _69_field), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = "));
                }
              }
            }
            {
              if (_source1.is_Some) {
                RAST._IAssignLhs value2 = _source1.dtor_value;
                if (value2.is_ExtractTuple) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _72_names = value2.dtor_names;
                  return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_72_names, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_73_name) => {
                    return _73_name;
                  })), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") = "));
                }
              }
            }
            {
              if (_source1.is_Some) {
                RAST._IAssignLhs value3 = _source1.dtor_value;
                if (value3.is_Index) {
                  RAST._IExpr _74_e = value3.dtor_expr;
                  Dafny.ISequence<RAST._IExpr> _75_indices = value3.dtor_indices;
                  _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs5 = (RAST.Expr.create_Call(_74_e, _75_indices)).LeftParentheses(_74_e);
                  Dafny.ISequence<Dafny.Rune> _76_leftP = _let_tmp_rhs5.dtor__0;
                  Dafny.ISequence<Dafny.Rune> _77_rightP = _let_tmp_rhs5.dtor__1;
                  return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_76_leftP, (_74_e)._ToString(ind)), _77_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[")), RAST.__default.SeqToString<RAST._IExpr>(_75_indices, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<RAST._IExpr>, Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>>>((_78_ind, _79_indices) => ((System.Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>)((_80_index) => {
                    return (_80_index)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_78_ind, RAST.__default.IND));
                  })))(ind, _75_indices), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]["))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("] = "));
                }
              }
            }
            {
              return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ = ");
            }
          }))();
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_66_lhs, (_65_expr)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      }
      {
        if (_source0.is_Labelled) {
          Dafny.ISequence<Dafny.Rune> _81_name = _source0.dtor_lbl;
          RAST._IExpr _82_underlying = _source0.dtor_underlying;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("'"), _81_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_82_underlying)._ToString(ind));
        }
      }
      {
        if (_source0.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _83_optLbl = _source0.dtor_optLbl;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source2 = _83_optLbl;
          {
            if (_source2.is_Some) {
              Dafny.ISequence<Dafny.Rune> _84_lbl = _source2.dtor_value;
              return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break '"), _84_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            }
          }
          {
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break;");
          }
        }
      }
      {
        if (_source0.is_Continue) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _85_optLbl = _source0.dtor_optLbl;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source3 = _85_optLbl;
          {
            if (_source3.is_Some) {
              Dafny.ISequence<Dafny.Rune> _86_lbl = _source3.dtor_value;
              return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue '"), _86_lbl), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
            }
          }
          {
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue;");
          }
        }
      }
      {
        if (_source0.is_Loop) {
          Std.Wrappers._IOption<RAST._IExpr> _87_optCond = _source0.dtor_optCond;
          RAST._IExpr _88_underlying = _source0.dtor_underlying;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
            Std.Wrappers._IOption<RAST._IExpr> _source4 = _87_optCond;
            {
              if (_source4.is_None) {
                return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("loop");
              }
            }
            {
              RAST._IExpr _89_c = _source4.dtor_value;
              return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while "), (_89_c)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)));
            }
          }))(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), ind), RAST.__default.IND), (_88_underlying)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      {
        if (_source0.is_For) {
          Dafny.ISequence<Dafny.Rune> _90_name = _source0.dtor_name;
          RAST._IExpr _91_range = _source0.dtor_range;
          RAST._IExpr _92_body = _source0.dtor_body;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for "), _90_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" in ")), (_91_range)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n")), ind), RAST.__default.IND), (_92_body)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }
      {
        if (_source0.is_Return) {
          Std.Wrappers._IOption<RAST._IExpr> _93_optExpr = _source0.dtor_optExpr;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"), (((_93_optExpr).is_Some) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" "), ((_93_optExpr).dtor_value)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND)))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"));
        }
      }
      {
        if (_source0.is_CallType) {
          RAST._IExpr _94_expr = _source0.dtor_obj;
          Dafny.ISequence<RAST._IType> _95_tpes = _source0.dtor_typeArguments;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs6 = (this).LeftParentheses(_94_expr);
          Dafny.ISequence<Dafny.Rune> _96_leftP = _let_tmp_rhs6.dtor__0;
          Dafny.ISequence<Dafny.Rune> _97_rightP = _let_tmp_rhs6.dtor__1;
          if ((_95_tpes).Equals(Dafny.Sequence<RAST._IType>.FromElements())) {
            return (_94_expr)._ToString(ind);
          } else {
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_96_leftP, (_94_expr)._ToString(ind)), _97_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::<")), RAST.__default.SeqToString<RAST._IType>(_95_tpes, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>>>((_98_ind) => ((System.Func<RAST._IType, Dafny.ISequence<Dafny.Rune>>)((_99_tpe) => {
              return (_99_tpe)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_98_ind, RAST.__default.IND));
            })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
          }
        }
      }
      {
        if (_source0.is_Call) {
          RAST._IExpr _100_expr = _source0.dtor_obj;
          Dafny.ISequence<RAST._IExpr> _101_args = _source0.dtor_arguments;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs7 = (this).LeftParentheses(_100_expr);
          Dafny.ISequence<Dafny.Rune> _102_leftP = _let_tmp_rhs7.dtor__0;
          Dafny.ISequence<Dafny.Rune> _103_rightP = _let_tmp_rhs7.dtor__1;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs8 = ((System.Func<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>>)(() => {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source5 = (_100_expr).RightMostIdentifier();
            {
              bool disjunctiveMatch0 = false;
              if (_source5.is_Some) {
                Dafny.ISequence<Dafny.Rune> value4 = _source5.dtor_value;
                if (object.Equals(value4, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))) {
                  disjunctiveMatch0 = true;
                }
              }
              if (_source5.is_Some) {
                Dafny.ISequence<Dafny.Rune> value5 = _source5.dtor_value;
                if (object.Equals(value5, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))) {
                  disjunctiveMatch0 = true;
                }
              }
              if (disjunctiveMatch0) {
                return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("["), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
              }
            }
            {
              bool disjunctiveMatch1 = false;
              if (_source5.is_Some) {
                Dafny.ISequence<Dafny.Rune> value6 = _source5.dtor_value;
                if (object.Equals(value6, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))) {
                  disjunctiveMatch1 = true;
                }
              }
              if (_source5.is_Some) {
                Dafny.ISequence<Dafny.Rune> value7 = _source5.dtor_value;
                if (object.Equals(value7, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))) {
                  disjunctiveMatch1 = true;
                }
              }
              if (disjunctiveMatch1) {
                return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
            }
            {
              return _System.Tuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            }
          }))();
          Dafny.ISequence<Dafny.Rune> _104_leftCallP = _let_tmp_rhs8.dtor__0;
          Dafny.ISequence<Dafny.Rune> _105_rightCallP = _let_tmp_rhs8.dtor__1;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_102_leftP, (_100_expr)._ToString(ind)), _103_rightP), _104_leftCallP), RAST.__default.SeqToString<RAST._IExpr>(_101_args, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<RAST._IExpr>, Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>>>((_106_ind, _107_args) => ((System.Func<RAST._IExpr, Dafny.ISequence<Dafny.Rune>>)((_108_arg) => {
            return (_108_arg)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(_106_ind, RAST.__default.IND));
          })))(ind, _101_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), _105_rightCallP);
        }
      }
      {
        if (_source0.is_Select) {
          RAST._IExpr _109_expression = _source0.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _110_name = _source0.dtor_name;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs9 = (this).LeftParentheses(_109_expression);
          Dafny.ISequence<Dafny.Rune> _111_leftP = _let_tmp_rhs9.dtor__0;
          Dafny.ISequence<Dafny.Rune> _112_rightP = _let_tmp_rhs9.dtor__1;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_111_leftP, (_109_expression)._ToString(ind)), _112_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), _110_name);
        }
      }
      {
        if (_source0.is_SelectIndex) {
          RAST._IExpr _113_expression = _source0.dtor_obj;
          RAST._IExpr _114_range = _source0.dtor_range;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs10 = (this).LeftParentheses(_113_expression);
          Dafny.ISequence<Dafny.Rune> _115_leftP = _let_tmp_rhs10.dtor__0;
          Dafny.ISequence<Dafny.Rune> _116_rightP = _let_tmp_rhs10.dtor__1;
          Dafny.ISequence<Dafny.Rune> _117_rangeStr = (_114_range)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND));
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_115_leftP, (_113_expression)._ToString(ind)), _116_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[")), _117_rangeStr), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("]"));
        }
      }
      {
        if (_source0.is_ExprFromPath) {
          RAST._IPath _118_path = _source0.dtor_path;
          return (_118_path)._ToString();
        }
      }
      {
        if (_source0.is_FunctionSelect) {
          RAST._IExpr _119_expression = _source0.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _120_name = _source0.dtor_name;
          _System._ITuple2<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs11 = (this).LeftParentheses(_119_expression);
          Dafny.ISequence<Dafny.Rune> _121_leftP = _let_tmp_rhs11.dtor__0;
          Dafny.ISequence<Dafny.Rune> _122_rightP = _let_tmp_rhs11.dtor__1;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_121_leftP, (_119_expression)._ToString(ind)), _122_rightP), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _120_name);
        }
      }
      {
        if (_source0.is_Lambda) {
          Dafny.ISequence<RAST._IFormal> _123_params = _source0.dtor_params;
          Std.Wrappers._IOption<RAST._IType> _124_retType = _source0.dtor_retType;
          RAST._IExpr _125_body = _source0.dtor_body;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |"), RAST.__default.SeqToString<RAST._IFormal>(_123_params, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>>>((_126_ind) => ((System.Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>)((_127_arg) => {
            return (_127_arg)._ToString(_126_ind);
          })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(","))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| ")), (((_124_retType).is_Some) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-> "), ((_124_retType).dtor_value)._ToString(ind))) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), ((((_124_retType).is_Some) && (!((_125_body).is_Block))) ? (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n"), ind), RAST.__default.IND), (_125_body)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"))) : ((_125_body)._ToString(ind))));
        }
      }
      {
        RAST._IExpr _128_r = _source0;
        return RAST.__default.AddIndent((_128_r).dtor_content, ind);
      }
    }
    public RAST._IExpr And(RAST._IExpr rhs2) {
      if (object.Equals(this, RAST.Expr.create_LiteralBool(true))) {
        return rhs2;
      } else {
        return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&"), this, rhs2, DAST.Format.BinaryOpFormat.create_NoFormat());
      }
    }
    public RAST._IExpr Equals(RAST._IExpr rhs2) {
      return RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), this, rhs2, DAST.Format.BinaryOpFormat.create_NoFormat());
    }
    public RAST._IExpr Then(RAST._IExpr rhs2) {
      if ((this).is_StmtExpr) {
        return RAST.Expr.create_StmtExpr((this).dtor_stmt, ((this).dtor_rhs).Then(rhs2));
      } else if (object.Equals(this, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))) {
        return rhs2;
      } else {
        return RAST.Expr.create_StmtExpr(this, rhs2);
      }
    }
    public RAST._IExpr Sel(Dafny.ISequence<Dafny.Rune> name) {
      return RAST.Expr.create_Select(this, name);
    }
    public RAST._IExpr FSel(Dafny.ISequence<Dafny.Rune> name) {
      return RAST.Expr.create_FunctionSelect(this, name);
    }
    public RAST._IExpr ApplyType(Dafny.ISequence<RAST._IType> typeArguments) {
      if ((new BigInteger((typeArguments).Count)).Sign == 0) {
        return this;
      } else {
        return RAST.Expr.create_CallType(this, typeArguments);
      }
    }
    public RAST._IExpr ApplyType1(RAST._IType typeArgument) {
      return RAST.Expr.create_CallType(this, Dafny.Sequence<RAST._IType>.FromElements(typeArgument));
    }
    public RAST._IExpr Apply(Dafny.ISequence<RAST._IExpr> arguments) {
      return RAST.Expr.create_Call(this, arguments);
    }
    public RAST._IExpr Apply1(RAST._IExpr argument) {
      return RAST.Expr.create_Call(this, Dafny.Sequence<RAST._IExpr>.FromElements(argument));
    }
    public RAST._IExpr Apply0() {
      return RAST.Expr.create_Call(this, Dafny.Sequence<RAST._IExpr>.FromElements());
    }
    public bool IsLhsIdentifier() {
      return ((this).is_Identifier) || (((this).is_Call) && (((((((this).dtor_obj).is_ExprFromPath) && (object.Equals(((this).dtor_obj).dtor_path, (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("modify!"))))) && ((new BigInteger(((this).dtor_arguments).Count)) == (BigInteger.One))) && ((((this).dtor_arguments).Select(BigInteger.Zero)).is_Identifier)) || ((((((this).dtor_obj).is_ExprFromPath) && (object.Equals(((this).dtor_obj).dtor_path, (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("md!"))))) && ((new BigInteger(((this).dtor_arguments).Count)) == (BigInteger.One))) && (Dafny.Helpers.Let<RAST._IExpr, bool>(((this).dtor_arguments).Select(BigInteger.Zero), _pat_let68_0 => Dafny.Helpers.Let<RAST._IExpr, bool>(_pat_let68_0, _0_lhs => (((_0_lhs).is_Call) && (((_0_lhs).dtor_obj).is_Select)) && ((((_0_lhs).dtor_obj).dtor_obj).is_Identifier)))))));
    }
    public Dafny.ISequence<Dafny.Rune> LhsIdentifierName() {
      if ((this).is_Identifier) {
        return (this).dtor_name;
      } else if ((((this).dtor_obj).is_ExprFromPath) && (object.Equals(((this).dtor_obj).dtor_path, (RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("modify!"))))) {
        return (((this).dtor_arguments).Select(BigInteger.Zero)).dtor_name;
      } else {
        return (((((this).dtor_arguments).Select(BigInteger.Zero)).dtor_obj).dtor_obj).dtor_name;
      }
    }
    public RAST._IExpr Clone() {
      return (RAST.Expr.create_Select(this, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))).Apply0();
    }
    public bool IsBorrow() {
      return ((this).is_UnaryOp) && (((this).dtor_op1).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")));
    }
    public RAST._IPrintingInfo printingInfo { get {
      RAST._IExpr _source0 = this;
      {
        if (_source0.is_RawExpr) {
          return RAST.PrintingInfo.create_UnknownPrecedence();
        }
      }
      {
        if (_source0.is_ExprFromType) {
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      {
        if (_source0.is_Identifier) {
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      {
        if (_source0.is_LiteralInt) {
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      {
        if (_source0.is_LiteralBool) {
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      {
        if (_source0.is_LiteralString) {
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      {
        if (_source0.is_UnaryOp) {
          Dafny.ISequence<Dafny.Rune> _0_op = _source0.dtor_op1;
          RAST._IExpr _1_underlying = _source0.dtor_underlying;
          DAST.Format._IUnaryOpFormat _2_format = _source0.dtor_format;
          Dafny.ISequence<Dafny.Rune> _source1 = _0_op;
          {
            if (object.Equals(_source1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("?"))) {
              return RAST.PrintingInfo.create_SuffixPrecedence(new BigInteger(5));
            }
          }
          {
            bool disjunctiveMatch0 = false;
            if (object.Equals(_source1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"))) {
              disjunctiveMatch0 = true;
            }
            if (object.Equals(_source1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))) {
              disjunctiveMatch0 = true;
            }
            if (object.Equals(_source1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"))) {
              disjunctiveMatch0 = true;
            }
            if (object.Equals(_source1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
              disjunctiveMatch0 = true;
            }
            if (object.Equals(_source1, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut"))) {
              disjunctiveMatch0 = true;
            }
            if (disjunctiveMatch0) {
              return RAST.PrintingInfo.create_Precedence(new BigInteger(6));
            }
          }
          {
            return RAST.PrintingInfo.create_UnknownPrecedence();
          }
        }
      }
      {
        if (_source0.is_Select) {
          RAST._IExpr _3_underlying = _source0.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _4_name = _source0.dtor_name;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
        }
      }
      {
        if (_source0.is_SelectIndex) {
          RAST._IExpr _5_underlying = _source0.dtor_obj;
          RAST._IExpr _6_range = _source0.dtor_range;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
        }
      }
      {
        if (_source0.is_ExprFromPath) {
          RAST._IPath _7_underlying = _source0.dtor_path;
          return RAST.PrintingInfo.create_Precedence(new BigInteger(2));
        }
      }
      {
        if (_source0.is_FunctionSelect) {
          RAST._IExpr _8_underlying = _source0.dtor_obj;
          Dafny.ISequence<Dafny.Rune> _9_name = _source0.dtor_name;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
        }
      }
      {
        if (_source0.is_CallType) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
        }
      }
      {
        if (_source0.is_Call) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(2), RAST.Associativity.create_LeftToRight());
        }
      }
      {
        if (_source0.is_TypeAscription) {
          RAST._IExpr _10_left = _source0.dtor_left;
          RAST._IType _11_tpe = _source0.dtor_tpe;
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(10), RAST.Associativity.create_LeftToRight());
        }
      }
      {
        if (_source0.is_TraitCast) {
          RAST._IType _12_leftTpe = _source0.dtor_leftTpe;
          RAST._IType _13_tpe = _source0.dtor_tpe;
          return RAST.PrintingInfo.create_Precedence(BigInteger.One);
        }
      }
      {
        if (_source0.is_BinaryOp) {
          Dafny.ISequence<Dafny.Rune> _14_op2 = _source0.dtor_op2;
          RAST._IExpr _15_left = _source0.dtor_left;
          RAST._IExpr _16_right = _source0.dtor_right;
          DAST.Format._IBinaryOpFormat _17_format = _source0.dtor_format2;
          Dafny.ISequence<Dafny.Rune> _source2 = _14_op2;
          {
            bool disjunctiveMatch1 = false;
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))) {
              disjunctiveMatch1 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/"))) {
              disjunctiveMatch1 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%"))) {
              disjunctiveMatch1 = true;
            }
            if (disjunctiveMatch1) {
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(20), RAST.Associativity.create_LeftToRight());
            }
          }
          {
            bool disjunctiveMatch2 = false;
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+"))) {
              disjunctiveMatch2 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-"))) {
              disjunctiveMatch2 = true;
            }
            if (disjunctiveMatch2) {
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(30), RAST.Associativity.create_LeftToRight());
            }
          }
          {
            bool disjunctiveMatch3 = false;
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<"))) {
              disjunctiveMatch3 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>"))) {
              disjunctiveMatch3 = true;
            }
            if (disjunctiveMatch3) {
              if (((_14_op2).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<"))) && ((_15_left).EndsWithTypeThatCanAcceptGenericsWhenPrinting())) {
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(9), RAST.Associativity.create_LeftToRight());
              } else {
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(40), RAST.Associativity.create_LeftToRight());
              }
            }
          }
          {
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(50), RAST.Associativity.create_LeftToRight());
            }
          }
          {
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^"))) {
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(60), RAST.Associativity.create_LeftToRight());
            }
          }
          {
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|"))) {
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(70), RAST.Associativity.create_LeftToRight());
            }
          }
          {
            bool disjunctiveMatch4 = false;
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="))) {
              disjunctiveMatch4 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!="))) {
              disjunctiveMatch4 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) {
              disjunctiveMatch4 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"))) {
              disjunctiveMatch4 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="))) {
              disjunctiveMatch4 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">="))) {
              disjunctiveMatch4 = true;
            }
            if (disjunctiveMatch4) {
              if ((((_14_op2).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"))) || ((_14_op2).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<=")))) && ((_15_left).EndsWithTypeThatCanAcceptGenericsWhenPrinting())) {
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(9), RAST.Associativity.create_LeftToRight());
              } else {
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(80), RAST.Associativity.create_RequiresParentheses());
              }
            }
          }
          {
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&"))) {
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(90), RAST.Associativity.create_LeftToRight());
            }
          }
          {
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||"))) {
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(100), RAST.Associativity.create_LeftToRight());
            }
          }
          {
            bool disjunctiveMatch5 = false;
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".."))) {
              disjunctiveMatch5 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("..="))) {
              disjunctiveMatch5 = true;
            }
            if (disjunctiveMatch5) {
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RequiresParentheses());
            }
          }
          {
            bool disjunctiveMatch6 = false;
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("="))) {
              disjunctiveMatch6 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+="))) {
              disjunctiveMatch6 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-="))) {
              disjunctiveMatch6 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*="))) {
              disjunctiveMatch6 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/="))) {
              disjunctiveMatch6 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%="))) {
              disjunctiveMatch6 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&="))) {
              disjunctiveMatch6 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|="))) {
              disjunctiveMatch6 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^="))) {
              disjunctiveMatch6 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<="))) {
              disjunctiveMatch6 = true;
            }
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>="))) {
              disjunctiveMatch6 = true;
            }
            if (disjunctiveMatch6) {
              if ((((_14_op2).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<="))) && ((_15_left).is_TypeAscription)) && (((_15_left).dtor_tpe).EndsWithNameThatCanAcceptGenerics())) {
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(9), RAST.Associativity.create_LeftToRight());
              } else {
                return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(110), RAST.Associativity.create_RightToLeft());
              }
            }
          }
          {
            if (object.Equals(_source2, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"))) {
              return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(120), RAST.Associativity.create_RightToLeft());
            }
          }
          {
            return RAST.PrintingInfo.create_PrecedenceAssociativity(BigInteger.Zero, RAST.Associativity.create_RequiresParentheses());
          }
        }
      }
      {
        if (_source0.is_Lambda) {
          return RAST.PrintingInfo.create_PrecedenceAssociativity(new BigInteger(300), RAST.Associativity.create_LeftToRight());
        }
      }
      {
        return RAST.PrintingInfo.create_UnknownPrecedence();
      }
    } }
  }
  public class Expr_RawExpr : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _content;
    public Expr_RawExpr(Dafny.ISequence<Dafny.Rune> content) : base() {
      this._content = content;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_RawExpr(_content);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_RawExpr;
      return oth != null && object.Equals(this._content, oth._content);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._content));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.RawExpr";
      s += "(";
      s += this._content.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_ExprFromType : Expr {
    public readonly RAST._IType _tpe;
    public Expr_ExprFromType(RAST._IType tpe) : base() {
      this._tpe = tpe;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_ExprFromType(_tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_ExprFromType;
      return oth != null && object.Equals(this._tpe, oth._tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.ExprFromType";
      s += "(";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ")";
      return s;
    }
  }
  public class Expr_Identifier : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public Expr_Identifier(Dafny.ISequence<Dafny.Rune> name) : base() {
      this._name = name;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Identifier(_name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Identifier;
      return oth != null && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Identifier";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_Match : Expr {
    public readonly RAST._IExpr _matchee;
    public readonly Dafny.ISequence<RAST._IMatchCase> _cases;
    public Expr_Match(RAST._IExpr matchee, Dafny.ISequence<RAST._IMatchCase> cases) : base() {
      this._matchee = matchee;
      this._cases = cases;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Match(_matchee, _cases);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Match;
      return oth != null && object.Equals(this._matchee, oth._matchee) && object.Equals(this._cases, oth._cases);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._matchee));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cases));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Match";
      s += "(";
      s += Dafny.Helpers.ToString(this._matchee);
      s += ", ";
      s += Dafny.Helpers.ToString(this._cases);
      s += ")";
      return s;
    }
  }
  public class Expr_StmtExpr : Expr {
    public readonly RAST._IExpr _stmt;
    public readonly RAST._IExpr _rhs;
    public Expr_StmtExpr(RAST._IExpr stmt, RAST._IExpr rhs) : base() {
      this._stmt = stmt;
      this._rhs = rhs;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_StmtExpr(_stmt, _rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_StmtExpr;
      return oth != null && object.Equals(this._stmt, oth._stmt) && object.Equals(this._rhs, oth._rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._stmt));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.StmtExpr";
      s += "(";
      s += Dafny.Helpers.ToString(this._stmt);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rhs);
      s += ")";
      return s;
    }
  }
  public class Expr_Block : Expr {
    public readonly RAST._IExpr _underlying;
    public Expr_Block(RAST._IExpr underlying) : base() {
      this._underlying = underlying;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Block(_underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Block;
      return oth != null && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Block";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Expr_StructBuild : Expr {
    public readonly RAST._IExpr _underlying;
    public readonly Dafny.ISequence<RAST._IAssignIdentifier> _assignments;
    public Expr_StructBuild(RAST._IExpr underlying, Dafny.ISequence<RAST._IAssignIdentifier> assignments) : base() {
      this._underlying = underlying;
      this._assignments = assignments;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_StructBuild(_underlying, _assignments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_StructBuild;
      return oth != null && object.Equals(this._underlying, oth._underlying) && object.Equals(this._assignments, oth._assignments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._assignments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.StructBuild";
      s += "(";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ", ";
      s += Dafny.Helpers.ToString(this._assignments);
      s += ")";
      return s;
    }
  }
  public class Expr_Tuple : Expr {
    public readonly Dafny.ISequence<RAST._IExpr> _arguments;
    public Expr_Tuple(Dafny.ISequence<RAST._IExpr> arguments) : base() {
      this._arguments = arguments;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Tuple(_arguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Tuple;
      return oth != null && object.Equals(this._arguments, oth._arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Tuple";
      s += "(";
      s += Dafny.Helpers.ToString(this._arguments);
      s += ")";
      return s;
    }
  }
  public class Expr_UnaryOp : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _op1;
    public readonly RAST._IExpr _underlying;
    public readonly DAST.Format._IUnaryOpFormat _format;
    public Expr_UnaryOp(Dafny.ISequence<Dafny.Rune> op1, RAST._IExpr underlying, DAST.Format._IUnaryOpFormat format) : base() {
      this._op1 = op1;
      this._underlying = underlying;
      this._format = format;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_UnaryOp(_op1, _underlying, _format);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_UnaryOp;
      return oth != null && object.Equals(this._op1, oth._op1) && object.Equals(this._underlying, oth._underlying) && object.Equals(this._format, oth._format);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._op1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._format));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.UnaryOp";
      s += "(";
      s += this._op1.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ", ";
      s += Dafny.Helpers.ToString(this._format);
      s += ")";
      return s;
    }
  }
  public class Expr_BinaryOp : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _op2;
    public readonly RAST._IExpr _left;
    public readonly RAST._IExpr _right;
    public readonly DAST.Format._IBinaryOpFormat _format2;
    public Expr_BinaryOp(Dafny.ISequence<Dafny.Rune> op2, RAST._IExpr left, RAST._IExpr right, DAST.Format._IBinaryOpFormat format2) : base() {
      this._op2 = op2;
      this._left = left;
      this._right = right;
      this._format2 = format2;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_BinaryOp(_op2, _left, _right, _format2);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_BinaryOp;
      return oth != null && object.Equals(this._op2, oth._op2) && object.Equals(this._left, oth._left) && object.Equals(this._right, oth._right) && object.Equals(this._format2, oth._format2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._op2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._right));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._format2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.BinaryOp";
      s += "(";
      s += this._op2.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._right);
      s += ", ";
      s += Dafny.Helpers.ToString(this._format2);
      s += ")";
      return s;
    }
  }
  public class Expr_TypeAscription : Expr {
    public readonly RAST._IExpr _left;
    public readonly RAST._IType _tpe;
    public Expr_TypeAscription(RAST._IExpr left, RAST._IType tpe) : base() {
      this._left = left;
      this._tpe = tpe;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_TypeAscription(_left, _tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_TypeAscription;
      return oth != null && object.Equals(this._left, oth._left) && object.Equals(this._tpe, oth._tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 10;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._left));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.TypeAscription";
      s += "(";
      s += Dafny.Helpers.ToString(this._left);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ")";
      return s;
    }
  }
  public class Expr_TraitCast : Expr {
    public readonly RAST._IType _leftTpe;
    public readonly RAST._IType _tpe;
    public Expr_TraitCast(RAST._IType leftTpe, RAST._IType tpe) : base() {
      this._leftTpe = leftTpe;
      this._tpe = tpe;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_TraitCast(_leftTpe, _tpe);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_TraitCast;
      return oth != null && object.Equals(this._leftTpe, oth._leftTpe) && object.Equals(this._tpe, oth._tpe);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 11;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._leftTpe));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._tpe));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.TraitCast";
      s += "(";
      s += Dafny.Helpers.ToString(this._leftTpe);
      s += ", ";
      s += Dafny.Helpers.ToString(this._tpe);
      s += ")";
      return s;
    }
  }
  public class Expr_LiteralInt : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _value;
    public Expr_LiteralInt(Dafny.ISequence<Dafny.Rune> @value) : base() {
      this._value = @value;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_LiteralInt(_value);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_LiteralInt;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 12;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.LiteralInt";
      s += "(";
      s += this._value.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_LiteralBool : Expr {
    public readonly bool _bvalue;
    public Expr_LiteralBool(bool bvalue) : base() {
      this._bvalue = bvalue;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_LiteralBool(_bvalue);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_LiteralBool;
      return oth != null && this._bvalue == oth._bvalue;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 13;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._bvalue));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.LiteralBool";
      s += "(";
      s += Dafny.Helpers.ToString(this._bvalue);
      s += ")";
      return s;
    }
  }
  public class Expr_LiteralString : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _value;
    public readonly bool _binary;
    public readonly bool _verbatim;
    public Expr_LiteralString(Dafny.ISequence<Dafny.Rune> @value, bool binary, bool verbatim) : base() {
      this._value = @value;
      this._binary = binary;
      this._verbatim = verbatim;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_LiteralString(_value, _binary, _verbatim);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_LiteralString;
      return oth != null && object.Equals(this._value, oth._value) && this._binary == oth._binary && this._verbatim == oth._verbatim;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 14;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._binary));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._verbatim));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.LiteralString";
      s += "(";
      s += this._value.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._binary);
      s += ", ";
      s += Dafny.Helpers.ToString(this._verbatim);
      s += ")";
      return s;
    }
  }
  public class Expr_DeclareVar : Expr {
    public readonly RAST._IDeclareType _declareType;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Std.Wrappers._IOption<RAST._IType> _optType;
    public readonly Std.Wrappers._IOption<RAST._IExpr> _optRhs;
    public Expr_DeclareVar(RAST._IDeclareType declareType, Dafny.ISequence<Dafny.Rune> name, Std.Wrappers._IOption<RAST._IType> optType, Std.Wrappers._IOption<RAST._IExpr> optRhs) : base() {
      this._declareType = declareType;
      this._name = name;
      this._optType = optType;
      this._optRhs = optRhs;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_DeclareVar(_declareType, _name, _optType, _optRhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_DeclareVar;
      return oth != null && object.Equals(this._declareType, oth._declareType) && object.Equals(this._name, oth._name) && object.Equals(this._optType, oth._optType) && object.Equals(this._optRhs, oth._optRhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 15;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._declareType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._optType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._optRhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.DeclareVar";
      s += "(";
      s += Dafny.Helpers.ToString(this._declareType);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._optType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._optRhs);
      s += ")";
      return s;
    }
  }
  public class Expr_Assign : Expr {
    public readonly Std.Wrappers._IOption<RAST._IAssignLhs> _names;
    public readonly RAST._IExpr _rhs;
    public Expr_Assign(Std.Wrappers._IOption<RAST._IAssignLhs> names, RAST._IExpr rhs) : base() {
      this._names = names;
      this._rhs = rhs;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Assign(_names, _rhs);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Assign;
      return oth != null && object.Equals(this._names, oth._names) && object.Equals(this._rhs, oth._rhs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 16;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._names));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rhs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Assign";
      s += "(";
      s += Dafny.Helpers.ToString(this._names);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rhs);
      s += ")";
      return s;
    }
  }
  public class Expr_IfExpr : Expr {
    public readonly RAST._IExpr _cond;
    public readonly RAST._IExpr _thn;
    public readonly RAST._IExpr _els;
    public Expr_IfExpr(RAST._IExpr cond, RAST._IExpr thn, RAST._IExpr els) : base() {
      this._cond = cond;
      this._thn = thn;
      this._els = els;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_IfExpr(_cond, _thn, _els);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_IfExpr;
      return oth != null && object.Equals(this._cond, oth._cond) && object.Equals(this._thn, oth._thn) && object.Equals(this._els, oth._els);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 17;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._thn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._els));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.IfExpr";
      s += "(";
      s += Dafny.Helpers.ToString(this._cond);
      s += ", ";
      s += Dafny.Helpers.ToString(this._thn);
      s += ", ";
      s += Dafny.Helpers.ToString(this._els);
      s += ")";
      return s;
    }
  }
  public class Expr_Loop : Expr {
    public readonly Std.Wrappers._IOption<RAST._IExpr> _optCond;
    public readonly RAST._IExpr _underlying;
    public Expr_Loop(Std.Wrappers._IOption<RAST._IExpr> optCond, RAST._IExpr underlying) : base() {
      this._optCond = optCond;
      this._underlying = underlying;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Loop(_optCond, _underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Loop;
      return oth != null && object.Equals(this._optCond, oth._optCond) && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 18;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._optCond));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Loop";
      s += "(";
      s += Dafny.Helpers.ToString(this._optCond);
      s += ", ";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Expr_For : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly RAST._IExpr _range;
    public readonly RAST._IExpr _body;
    public Expr_For(Dafny.ISequence<Dafny.Rune> name, RAST._IExpr range, RAST._IExpr body) : base() {
      this._name = name;
      this._range = range;
      this._body = body;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_For(_name, _range, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_For;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._range, oth._range) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 19;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._range));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.For";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._range);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }
  public class Expr_Labelled : Expr {
    public readonly Dafny.ISequence<Dafny.Rune> _lbl;
    public readonly RAST._IExpr _underlying;
    public Expr_Labelled(Dafny.ISequence<Dafny.Rune> lbl, RAST._IExpr underlying) : base() {
      this._lbl = lbl;
      this._underlying = underlying;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Labelled(_lbl, _underlying);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Labelled;
      return oth != null && object.Equals(this._lbl, oth._lbl) && object.Equals(this._underlying, oth._underlying);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 20;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lbl));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._underlying));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Labelled";
      s += "(";
      s += this._lbl.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._underlying);
      s += ")";
      return s;
    }
  }
  public class Expr_Break : Expr {
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _optLbl;
    public Expr_Break(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> optLbl) : base() {
      this._optLbl = optLbl;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Break(_optLbl);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Break;
      return oth != null && object.Equals(this._optLbl, oth._optLbl);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 21;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._optLbl));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Break";
      s += "(";
      s += Dafny.Helpers.ToString(this._optLbl);
      s += ")";
      return s;
    }
  }
  public class Expr_Continue : Expr {
    public readonly Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _optLbl;
    public Expr_Continue(Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> optLbl) : base() {
      this._optLbl = optLbl;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Continue(_optLbl);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Continue;
      return oth != null && object.Equals(this._optLbl, oth._optLbl);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 22;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._optLbl));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Continue";
      s += "(";
      s += Dafny.Helpers.ToString(this._optLbl);
      s += ")";
      return s;
    }
  }
  public class Expr_Return : Expr {
    public readonly Std.Wrappers._IOption<RAST._IExpr> _optExpr;
    public Expr_Return(Std.Wrappers._IOption<RAST._IExpr> optExpr) : base() {
      this._optExpr = optExpr;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Return(_optExpr);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Return;
      return oth != null && object.Equals(this._optExpr, oth._optExpr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 23;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._optExpr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Return";
      s += "(";
      s += Dafny.Helpers.ToString(this._optExpr);
      s += ")";
      return s;
    }
  }
  public class Expr_CallType : Expr {
    public readonly RAST._IExpr _obj;
    public readonly Dafny.ISequence<RAST._IType> _typeArguments;
    public Expr_CallType(RAST._IExpr obj, Dafny.ISequence<RAST._IType> typeArguments) : base() {
      this._obj = obj;
      this._typeArguments = typeArguments;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_CallType(_obj, _typeArguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_CallType;
      return oth != null && object.Equals(this._obj, oth._obj) && object.Equals(this._typeArguments, oth._typeArguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 24;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeArguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.CallType";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeArguments);
      s += ")";
      return s;
    }
  }
  public class Expr_Call : Expr {
    public readonly RAST._IExpr _obj;
    public readonly Dafny.ISequence<RAST._IExpr> _arguments;
    public Expr_Call(RAST._IExpr obj, Dafny.ISequence<RAST._IExpr> arguments) : base() {
      this._obj = obj;
      this._arguments = arguments;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Call(_obj, _arguments);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Call;
      return oth != null && object.Equals(this._obj, oth._obj) && object.Equals(this._arguments, oth._arguments);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 25;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arguments));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Call";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ", ";
      s += Dafny.Helpers.ToString(this._arguments);
      s += ")";
      return s;
    }
  }
  public class Expr_Select : Expr {
    public readonly RAST._IExpr _obj;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public Expr_Select(RAST._IExpr obj, Dafny.ISequence<Dafny.Rune> name) : base() {
      this._obj = obj;
      this._name = name;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Select(_obj, _name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Select;
      return oth != null && object.Equals(this._obj, oth._obj) && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 26;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Select";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_SelectIndex : Expr {
    public readonly RAST._IExpr _obj;
    public readonly RAST._IExpr _range;
    public Expr_SelectIndex(RAST._IExpr obj, RAST._IExpr range) : base() {
      this._obj = obj;
      this._range = range;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_SelectIndex(_obj, _range);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_SelectIndex;
      return oth != null && object.Equals(this._obj, oth._obj) && object.Equals(this._range, oth._range);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 27;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._range));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.SelectIndex";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ", ";
      s += Dafny.Helpers.ToString(this._range);
      s += ")";
      return s;
    }
  }
  public class Expr_ExprFromPath : Expr {
    public readonly RAST._IPath _path;
    public Expr_ExprFromPath(RAST._IPath path) : base() {
      this._path = path;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_ExprFromPath(_path);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_ExprFromPath;
      return oth != null && object.Equals(this._path, oth._path);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 28;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._path));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.ExprFromPath";
      s += "(";
      s += Dafny.Helpers.ToString(this._path);
      s += ")";
      return s;
    }
  }
  public class Expr_FunctionSelect : Expr {
    public readonly RAST._IExpr _obj;
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public Expr_FunctionSelect(RAST._IExpr obj, Dafny.ISequence<Dafny.Rune> name) : base() {
      this._obj = obj;
      this._name = name;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_FunctionSelect(_obj, _name);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_FunctionSelect;
      return oth != null && object.Equals(this._obj, oth._obj) && object.Equals(this._name, oth._name);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 29;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.FunctionSelect";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ", ";
      s += this._name.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class Expr_Lambda : Expr {
    public readonly Dafny.ISequence<RAST._IFormal> _params;
    public readonly Std.Wrappers._IOption<RAST._IType> _retType;
    public readonly RAST._IExpr _body;
    public Expr_Lambda(Dafny.ISequence<RAST._IFormal> @params, Std.Wrappers._IOption<RAST._IType> retType, RAST._IExpr body) : base() {
      this._params = @params;
      this._retType = retType;
      this._body = body;
    }
    public override _IExpr DowncastClone() {
      if (this is _IExpr dt) { return dt; }
      return new Expr_Lambda(_params, _retType, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Expr_Lambda;
      return oth != null && object.Equals(this._params, oth._params) && object.Equals(this._retType, oth._retType) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 30;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._params));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._retType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Expr.Lambda";
      s += "(";
      s += Dafny.Helpers.ToString(this._params);
      s += ", ";
      s += Dafny.Helpers.ToString(this._retType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
  }

  public interface _IFn {
    bool is_Fn { get; }
    Dafny.ISequence<Dafny.Rune> dtor_name { get; }
    Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams { get; }
    Dafny.ISequence<RAST._IFormal> dtor_formals { get; }
    Std.Wrappers._IOption<RAST._IType> dtor_returnType { get; }
    Std.Wrappers._IOption<RAST._IExpr> dtor_body { get; }
    _IFn DowncastClone();
    Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind);
  }
  public class Fn : _IFn {
    public readonly Dafny.ISequence<Dafny.Rune> _name;
    public readonly Dafny.ISequence<RAST._ITypeParamDecl> _typeParams;
    public readonly Dafny.ISequence<RAST._IFormal> _formals;
    public readonly Std.Wrappers._IOption<RAST._IType> _returnType;
    public readonly Std.Wrappers._IOption<RAST._IExpr> _body;
    public Fn(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IFormal> formals, Std.Wrappers._IOption<RAST._IType> returnType, Std.Wrappers._IOption<RAST._IExpr> body) {
      this._name = name;
      this._typeParams = typeParams;
      this._formals = formals;
      this._returnType = returnType;
      this._body = body;
    }
    public _IFn DowncastClone() {
      if (this is _IFn dt) { return dt; }
      return new Fn(_name, _typeParams, _formals, _returnType, _body);
    }
    public override bool Equals(object other) {
      var oth = other as RAST.Fn;
      return oth != null && object.Equals(this._name, oth._name) && object.Equals(this._typeParams, oth._typeParams) && object.Equals(this._formals, oth._formals) && object.Equals(this._returnType, oth._returnType) && object.Equals(this._body, oth._body);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._name));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._typeParams));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._formals));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._returnType));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._body));
      return (int) hash;
    }
    public override string ToString() {
      string s = "RAST.Fn.Fn";
      s += "(";
      s += this._name.ToVerbatimString(true);
      s += ", ";
      s += Dafny.Helpers.ToString(this._typeParams);
      s += ", ";
      s += Dafny.Helpers.ToString(this._formals);
      s += ", ";
      s += Dafny.Helpers.ToString(this._returnType);
      s += ", ";
      s += Dafny.Helpers.ToString(this._body);
      s += ")";
      return s;
    }
    private static readonly RAST._IFn theDefault = create(Dafny.Sequence<Dafny.Rune>.Empty, Dafny.Sequence<RAST._ITypeParamDecl>.Empty, Dafny.Sequence<RAST._IFormal>.Empty, Std.Wrappers.Option<RAST._IType>.Default(), Std.Wrappers.Option<RAST._IExpr>.Default());
    public static RAST._IFn Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<RAST._IFn> _TYPE = new Dafny.TypeDescriptor<RAST._IFn>(RAST.Fn.Default());
    public static Dafny.TypeDescriptor<RAST._IFn> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IFn create(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IFormal> formals, Std.Wrappers._IOption<RAST._IType> returnType, Std.Wrappers._IOption<RAST._IExpr> body) {
      return new Fn(name, typeParams, formals, returnType, body);
    }
    public static _IFn create_Fn(Dafny.ISequence<Dafny.Rune> name, Dafny.ISequence<RAST._ITypeParamDecl> typeParams, Dafny.ISequence<RAST._IFormal> formals, Std.Wrappers._IOption<RAST._IType> returnType, Std.Wrappers._IOption<RAST._IExpr> body) {
      return create(name, typeParams, formals, returnType, body);
    }
    public bool is_Fn { get { return true; } }
    public Dafny.ISequence<Dafny.Rune> dtor_name {
      get {
        return this._name;
      }
    }
    public Dafny.ISequence<RAST._ITypeParamDecl> dtor_typeParams {
      get {
        return this._typeParams;
      }
    }
    public Dafny.ISequence<RAST._IFormal> dtor_formals {
      get {
        return this._formals;
      }
    }
    public Std.Wrappers._IOption<RAST._IType> dtor_returnType {
      get {
        return this._returnType;
      }
    }
    public Std.Wrappers._IOption<RAST._IExpr> dtor_body {
      get {
        return this._body;
      }
    }
    public Dafny.ISequence<Dafny.Rune> _ToString(Dafny.ISequence<Dafny.Rune> ind) {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn "), (this).dtor_name), RAST.TypeParamDecl.ToStringMultiple((this).dtor_typeParams, ind)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), RAST.__default.SeqToString<RAST._IFormal>((this).dtor_formals, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.Rune>, Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>>>((_0_ind) => ((System.Func<RAST._IFormal, Dafny.ISequence<Dafny.Rune>>)((_1_formal) => {
        return (_1_formal)._ToString(_0_ind);
      })))(ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")), ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
        Std.Wrappers._IOption<RAST._IType> _source0 = (this).dtor_returnType;
        {
          if (_source0.is_Some) {
            RAST._IType _2_t = _source0.dtor_value;
            return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" -> "), (_2_t)._ToString(ind));
          }
        }
        {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
      }))()), ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
        Std.Wrappers._IOption<RAST._IExpr> _source1 = (this).dtor_body;
        {
          if (_source1.is_None) {
            return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";");
          }
        }
        {
          RAST._IExpr _3_body = _source1.dtor_value;
          return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" {\n"), ind), RAST.__default.IND), (_3_body)._ToString(Dafny.Sequence<Dafny.Rune>.Concat(ind, RAST.__default.IND))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")), ind), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
      }))());
    }
  }
} // end of namespace RAST