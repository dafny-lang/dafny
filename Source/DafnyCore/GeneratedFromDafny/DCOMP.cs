// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace DCOMP {

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
          if (((i).Select(BigInteger.One)) != (new Dafny.Rune('_'))) {
            return true;
          } else {
            Dafny.ISequence<Dafny.Rune> _in122 = (i).Drop(new BigInteger(2));
            i = _in122;
            goto TAIL_CALL_START;
          }
        } else {
          return true;
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _in123 = (i).Drop(BigInteger.One);
        i = _in123;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> idiomatic__rust(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1137___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1137___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1137___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1137___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(new BigInteger(2));
        i = _in124;
        goto TAIL_CALL_START;
      } else {
        _1137___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1137___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1138___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1138___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1138___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1138___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in126 = (i).Drop(BigInteger.One);
        i = _in126;
        goto TAIL_CALL_START;
      } else {
        _1138___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1138___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in127 = (i).Drop(BigInteger.One);
        i = _in127;
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
      return ((((new BigInteger((i).Count)).Sign == 1) && (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_')))) && (!(DCOMP.__default.has__special((i).Drop(BigInteger.One))))) && (!((new BigInteger((i).Count)) >= (new BigInteger(2))) || (((i).Select(BigInteger.One)) != (new Dafny.Rune('T'))));
    }
    public static bool is__idiomatic__rust__id(Dafny.ISequence<Dafny.Rune> i) {
      return ((((new BigInteger((i).Count)).Sign == 1) && (!(DCOMP.__default.has__special(i)))) && (!(DCOMP.__default.reserved__rust).Contains(i))) && (!(DCOMP.__default.reserved__rust__need__prefix).Contains(i));
    }
    public static Dafny.ISequence<Dafny.Rune> escapeName(Dafny.ISequence<Dafny.Rune> n) {
      return DCOMP.__default.escapeIdent((n));
    }
    public static Dafny.ISequence<Dafny.Rune> escapeIdent(Dafny.ISequence<Dafny.Rune> i) {
      if (DCOMP.__default.is__tuple__numeric(i)) {
        return i;
      } else if (DCOMP.__default.is__tuple__builder(i)) {
        return DCOMP.__default.better__tuple__builder__name(i);
      } else if (((i).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) || ((i).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Self")))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), i);
      } else if ((DCOMP.__default.reserved__rust).Contains(i)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#"), i);
      } else if (DCOMP.__default.is__idiomatic__rust__id(i)) {
        return DCOMP.__default.idiomatic__rust(i);
      } else if (DCOMP.__default.is__dafny__generated__id(i)) {
        return i;
      } else {
        Dafny.ISequence<Dafny.Rune> _1139_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1139_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeVar(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1140_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1140_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1140_r);
      } else {
        return DCOMP.__default.escapeName(f);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeDtor(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1141_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1141_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1141_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": r#_")), _1141_r);
      } else {
        return DCOMP.__default.escapeName(f);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeType(Dafny.ISequence<Dafny.Rune> n) {
      return DCOMP.__default.escapeName(n);
    }
    public static Dafny.ISequence<Dafny.Rune> AddAssignedPrefix(Dafny.ISequence<Dafny.Rune> rustName) {
      if (((new BigInteger((rustName).Count)) >= (new BigInteger(2))) && (((rustName).Subsequence(BigInteger.Zero, new BigInteger(2))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#")))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.ASSIGNED__PREFIX, (rustName).Drop(new BigInteger(2)));
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.__default.ASSIGNED__PREFIX, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_")), rustName);
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethodAux(Dafny.ISequence<DAST._IType> rs, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      var _pat_let_tv139 = dafnyName;
      var _pat_let_tv140 = rs;
      var _pat_let_tv141 = dafnyName;
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _1142_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source52 = (rs).Select(BigInteger.Zero);
          bool unmatched52 = true;
          if (unmatched52) {
            if (_source52.is_UserDefined) {
              DAST._IResolvedType _1143_resolvedType = _source52.dtor_resolved;
              unmatched52 = false;
              return DCOMP.__default.TraitTypeContainingMethod(_1143_resolvedType, _pat_let_tv139);
            }
          }
          if (unmatched52) {
            unmatched52 = false;
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
          throw new System.Exception("unexpected control point");
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source53 = _1142_res;
        bool unmatched53 = true;
        if (unmatched53) {
          if (_source53.is_Some) {
            unmatched53 = false;
            return _1142_res;
          }
        }
        if (unmatched53) {
          unmatched53 = false;
          return DCOMP.__default.TraitTypeContainingMethodAux((_pat_let_tv140).Drop(BigInteger.One), _pat_let_tv141);
        }
        throw new System.Exception("unexpected control point");
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethod(DAST._IResolvedType r, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DAST._IResolvedType _let_tmp_rhs53 = r;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1144_path = _let_tmp_rhs53.dtor_path;
      Dafny.ISequence<DAST._IType> _1145_typeArgs = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedTypeBase _1146_kind = _let_tmp_rhs53.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1147_attributes = _let_tmp_rhs53.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1148_properMethods = _let_tmp_rhs53.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1149_extendedTypes = _let_tmp_rhs53.dtor_extendedTypes;
      if ((_1148_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1149_extendedTypes, dafnyName);
      }
    }
    public static Std.Wrappers._IOption<DCOMP._IExternAttribute> OptExtern(DAST._IAttribute attr, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      if (((attr).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) {
        return Std.Wrappers.Option<DCOMP._IExternAttribute>.create_Some((((new BigInteger(((attr).dtor_args).Count)).Sign == 0) ? (DCOMP.ExternAttribute.create_SimpleExtern(DCOMP.__default.escapeName(dafnyName))) : ((((new BigInteger(((attr).dtor_args).Count)) == (BigInteger.One)) ? (DCOMP.ExternAttribute.create_SimpleExtern(((attr).dtor_args).Select(BigInteger.Zero))) : ((((new BigInteger(((attr).dtor_args).Count)) == (new BigInteger(2))) ? (DCOMP.ExternAttribute.create_AdvancedExtern(DCOMP.__default.ReplaceDotByDoubleColon(((attr).dtor_args).Select(BigInteger.Zero)), ((attr).dtor_args).Select(BigInteger.One))) : (DCOMP.ExternAttribute.create_UnsupportedExtern(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{:extern} supports only 0, 1 or 2 attributes, got "), Std.Strings.__default.OfNat(new BigInteger(((attr).dtor_args).Count)))))))))));
      } else {
        return Std.Wrappers.Option<DCOMP._IExternAttribute>.create_None();
      }
    }
    public static Dafny.ISequence<Dafny.Rune> ReplaceDotByDoubleColon(Dafny.ISequence<Dafny.Rune> s) {
      Dafny.ISequence<Dafny.Rune> _1150___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1150___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((s).Select(BigInteger.Zero)) == (new Dafny.Rune(' '))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1150___accumulator, s);
      } else {
        _1150___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1150___accumulator, ((((s).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")) : (Dafny.Sequence<Dafny.Rune>.FromElements((s).Select(BigInteger.Zero)))));
        Dafny.ISequence<Dafny.Rune> _in128 = (s).Drop(BigInteger.One);
        s = _in128;
        goto TAIL_CALL_START;
      }
    }
    public static DCOMP._IExternAttribute ExtractExtern(Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DCOMP._IExternAttribute res = DCOMP.ExternAttribute.Default();
      BigInteger _hi5 = new BigInteger((attributes).Count);
      for (BigInteger _1151_i = BigInteger.Zero; _1151_i < _hi5; _1151_i++) {
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _1152_attr;
        _1152_attr = DCOMP.__default.OptExtern((attributes).Select(_1151_i), dafnyName);
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _source54 = _1152_attr;
        bool unmatched54 = true;
        if (unmatched54) {
          if (_source54.is_Some) {
            DCOMP._IExternAttribute _1153_n = _source54.dtor_value;
            unmatched54 = false;
            res = _1153_n;
            return res;
          }
        }
        if (unmatched54) {
          unmatched54 = false;
        }
      }
      res = DCOMP.ExternAttribute.create_NoExtern();
      return res;
    }
    public static DCOMP._IExternAttribute ExtractExternMod(DAST._IModule mod) {
      return DCOMP.__default.ExtractExtern((mod).dtor_attributes, (mod).dtor_name);
    }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("async"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("await"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("const"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("else"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("enum"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("loop"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mod"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mut"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ref"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("static"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("struct"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("trait"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("union"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("use"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("where"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Keywords"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abstract"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("become"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("box"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("do"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("final"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("macro"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("override"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("priv"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("try"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("typeof"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsized"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("virtual"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("yield"));
    } }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust__need__prefix { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u8"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u16"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u32"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u64"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u128"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i8"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i16"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i32"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i64"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i128"));
    } }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__fields { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"));
    } }
    public static Dafny.ISequence<Dafny.Rune> ASSIGNED__PREFIX { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_set");
    } }
    public static Dafny.ISequence<Dafny.Rune> IND { get {
      return RAST.__default.IND;
    } }
    public static DAST._IAttribute AttributeOwned { get {
      return DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("owned"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
    } }
  }

  public interface _IOwnership {
    bool is_OwnershipOwned { get; }
    bool is_OwnershipOwnedBox { get; }
    bool is_OwnershipBorrowed { get; }
    bool is_OwnershipBorrowedMut { get; }
    bool is_OwnershipAutoBorrowed { get; }
    _IOwnership DowncastClone();
  }
  public abstract class Ownership : _IOwnership {
    public Ownership() {
    }
    private static readonly DCOMP._IOwnership theDefault = create_OwnershipOwned();
    public static DCOMP._IOwnership Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DCOMP._IOwnership> _TYPE = new Dafny.TypeDescriptor<DCOMP._IOwnership>(DCOMP.Ownership.Default());
    public static Dafny.TypeDescriptor<DCOMP._IOwnership> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IOwnership create_OwnershipOwned() {
      return new Ownership_OwnershipOwned();
    }
    public static _IOwnership create_OwnershipOwnedBox() {
      return new Ownership_OwnershipOwnedBox();
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
    public bool is_OwnershipOwnedBox { get { return this is Ownership_OwnershipOwnedBox; } }
    public bool is_OwnershipBorrowed { get { return this is Ownership_OwnershipBorrowed; } }
    public bool is_OwnershipBorrowedMut { get { return this is Ownership_OwnershipBorrowedMut; } }
    public bool is_OwnershipAutoBorrowed { get { return this is Ownership_OwnershipAutoBorrowed; } }
    public static System.Collections.Generic.IEnumerable<_IOwnership> AllSingletonConstructors {
      get {
        yield return Ownership.create_OwnershipOwned();
        yield return Ownership.create_OwnershipOwnedBox();
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
      var oth = other as DCOMP.Ownership_OwnershipOwned;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Ownership.OwnershipOwned";
      return s;
    }
  }
  public class Ownership_OwnershipOwnedBox : Ownership {
    public Ownership_OwnershipOwnedBox() : base() {
    }
    public override _IOwnership DowncastClone() {
      if (this is _IOwnership dt) { return dt; }
      return new Ownership_OwnershipOwnedBox();
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.Ownership_OwnershipOwnedBox;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Ownership.OwnershipOwnedBox";
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
      var oth = other as DCOMP.Ownership_OwnershipBorrowed;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Ownership.OwnershipBorrowed";
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
      var oth = other as DCOMP.Ownership_OwnershipBorrowedMut;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Ownership.OwnershipBorrowedMut";
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
      var oth = other as DCOMP.Ownership_OwnershipAutoBorrowed;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Ownership.OwnershipAutoBorrowed";
      return s;
    }
  }

  public interface _IEnvironment {
    bool is_Environment { get; }
    Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> dtor_names { get; }
    Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> dtor_types { get; }
    _IEnvironment DowncastClone();
    DCOMP._IEnvironment ToOwned();
    bool CanReadWithoutClone(Dafny.ISequence<Dafny.Rune> name);
    bool HasCloneSemantics(Dafny.ISequence<Dafny.Rune> name);
    Std.Wrappers._IOption<RAST._IType> GetType(Dafny.ISequence<Dafny.Rune> name);
    bool IsBorrowed(Dafny.ISequence<Dafny.Rune> name);
    bool IsBorrowedMut(Dafny.ISequence<Dafny.Rune> name);
    DCOMP._IEnvironment AddAssigned(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe);
    DCOMP._IEnvironment merge(DCOMP._IEnvironment other);
    DCOMP._IEnvironment RemoveAssigned(Dafny.ISequence<Dafny.Rune> name);
  }
  public class Environment : _IEnvironment {
    public readonly Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _names;
    public readonly Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _types;
    public Environment(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> types) {
      this._names = names;
      this._types = types;
    }
    public _IEnvironment DowncastClone() {
      if (this is _IEnvironment dt) { return dt; }
      return new Environment(_names, _types);
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.Environment;
      return oth != null && object.Equals(this._names, oth._names) && object.Equals(this._types, oth._types);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._names));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._types));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.Environment.Environment";
      s += "(";
      s += Dafny.Helpers.ToString(this._names);
      s += ", ";
      s += Dafny.Helpers.ToString(this._types);
      s += ")";
      return s;
    }
    private static readonly DCOMP._IEnvironment theDefault = create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Empty, Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Empty);
    public static DCOMP._IEnvironment Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DCOMP._IEnvironment> _TYPE = new Dafny.TypeDescriptor<DCOMP._IEnvironment>(DCOMP.Environment.Default());
    public static Dafny.TypeDescriptor<DCOMP._IEnvironment> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEnvironment create(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> types) {
      return new Environment(names, types);
    }
    public static _IEnvironment create_Environment(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> names, Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> types) {
      return create(names, types);
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
    public DCOMP._IEnvironment ToOwned() {
      DCOMP._IEnvironment _1154_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1155_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll6 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1156_k = (Dafny.ISequence<Dafny.Rune>)_compr_6;
          if (((this).dtor_types).Contains(_1156_k)) {
            _coll6.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_1156_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_1156_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll6);
      }))();
      return DCOMP.Environment.create((_1154_dt__update__tmp_h0).dtor_names, _1155_dt__update_htypes_h0);
    }
    public static DCOMP._IEnvironment Empty() {
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements());
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
    public DCOMP._IEnvironment AddAssigned(Dafny.ISequence<Dafny.Rune> name, RAST._IType tpe)
    {
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((this).dtor_names, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(name)), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update((this).dtor_types, name, tpe));
    }
    public DCOMP._IEnvironment merge(DCOMP._IEnvironment other) {
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat((this).dtor_names, (other).dtor_names), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge((this).dtor_types, (other).dtor_types));
    }
    public DCOMP._IEnvironment RemoveAssigned(Dafny.ISequence<Dafny.Rune> name) {
      BigInteger _1157_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1157_indexInEnv), ((this).dtor_names).Drop((_1157_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
    }
  }

  public interface _IObjectType {
    bool is_RawPointers { get; }
    bool is_RcMut { get; }
    _IObjectType DowncastClone();
  }
  public abstract class ObjectType : _IObjectType {
    public ObjectType() {
    }
    private static readonly DCOMP._IObjectType theDefault = create_RawPointers();
    public static DCOMP._IObjectType Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DCOMP._IObjectType> _TYPE = new Dafny.TypeDescriptor<DCOMP._IObjectType>(DCOMP.ObjectType.Default());
    public static Dafny.TypeDescriptor<DCOMP._IObjectType> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IObjectType create_RawPointers() {
      return new ObjectType_RawPointers();
    }
    public static _IObjectType create_RcMut() {
      return new ObjectType_RcMut();
    }
    public bool is_RawPointers { get { return this is ObjectType_RawPointers; } }
    public bool is_RcMut { get { return this is ObjectType_RcMut; } }
    public static System.Collections.Generic.IEnumerable<_IObjectType> AllSingletonConstructors {
      get {
        yield return ObjectType.create_RawPointers();
        yield return ObjectType.create_RcMut();
      }
    }
    public abstract _IObjectType DowncastClone();
  }
  public class ObjectType_RawPointers : ObjectType {
    public ObjectType_RawPointers() : base() {
    }
    public override _IObjectType DowncastClone() {
      if (this is _IObjectType dt) { return dt; }
      return new ObjectType_RawPointers();
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.ObjectType_RawPointers;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.ObjectType.RawPointers";
      return s;
    }
  }
  public class ObjectType_RcMut : ObjectType {
    public ObjectType_RcMut() : base() {
    }
    public override _IObjectType DowncastClone() {
      if (this is _IObjectType dt) { return dt; }
      return new ObjectType_RcMut();
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.ObjectType_RcMut;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.ObjectType.RcMut";
      return s;
    }
  }

  public interface _IGenTypeContext {
    bool is_GenTypeContext { get; }
    bool dtor_inBinding { get; }
    bool dtor_inFn { get; }
    bool dtor_forTraitParents { get; }
    _IGenTypeContext DowncastClone();
  }
  public class GenTypeContext : _IGenTypeContext {
    public readonly bool _inBinding;
    public readonly bool _inFn;
    public readonly bool _forTraitParents;
    public GenTypeContext(bool inBinding, bool inFn, bool forTraitParents) {
      this._inBinding = inBinding;
      this._inFn = inFn;
      this._forTraitParents = forTraitParents;
    }
    public _IGenTypeContext DowncastClone() {
      if (this is _IGenTypeContext dt) { return dt; }
      return new GenTypeContext(_inBinding, _inFn, _forTraitParents);
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.GenTypeContext;
      return oth != null && this._inBinding == oth._inBinding && this._inFn == oth._inFn && this._forTraitParents == oth._forTraitParents;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._inBinding));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._inFn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._forTraitParents));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.GenTypeContext.GenTypeContext";
      s += "(";
      s += Dafny.Helpers.ToString(this._inBinding);
      s += ", ";
      s += Dafny.Helpers.ToString(this._inFn);
      s += ", ";
      s += Dafny.Helpers.ToString(this._forTraitParents);
      s += ")";
      return s;
    }
    private static readonly DCOMP._IGenTypeContext theDefault = create(false, false, false);
    public static DCOMP._IGenTypeContext Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DCOMP._IGenTypeContext> _TYPE = new Dafny.TypeDescriptor<DCOMP._IGenTypeContext>(DCOMP.GenTypeContext.Default());
    public static Dafny.TypeDescriptor<DCOMP._IGenTypeContext> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IGenTypeContext create(bool inBinding, bool inFn, bool forTraitParents) {
      return new GenTypeContext(inBinding, inFn, forTraitParents);
    }
    public static _IGenTypeContext create_GenTypeContext(bool inBinding, bool inFn, bool forTraitParents) {
      return create(inBinding, inFn, forTraitParents);
    }
    public bool is_GenTypeContext { get { return true; } }
    public bool dtor_inBinding {
      get {
        return this._inBinding;
      }
    }
    public bool dtor_inFn {
      get {
        return this._inFn;
      }
    }
    public bool dtor_forTraitParents {
      get {
        return this._forTraitParents;
      }
    }
    public static DCOMP._IGenTypeContext InBinding() {
      return DCOMP.GenTypeContext.create(true, false, false);
    }
    public static DCOMP._IGenTypeContext InFn() {
      return DCOMP.GenTypeContext.create(false, true, false);
    }
    public static DCOMP._IGenTypeContext ForTraitParents() {
      return DCOMP.GenTypeContext.create(false, false, true);
    }
    public static DCOMP._IGenTypeContext @default() {
      return DCOMP.GenTypeContext.create(false, false, false);
    }
  }

  public interface _ISelfInfo {
    bool is_NoSelf { get; }
    bool is_ThisTyped { get; }
    Dafny.ISequence<Dafny.Rune> dtor_rSelfName { get; }
    DAST._IType dtor_dafnyType { get; }
    _ISelfInfo DowncastClone();
    bool IsSelf();
  }
  public abstract class SelfInfo : _ISelfInfo {
    public SelfInfo() {
    }
    private static readonly DCOMP._ISelfInfo theDefault = create_NoSelf();
    public static DCOMP._ISelfInfo Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DCOMP._ISelfInfo> _TYPE = new Dafny.TypeDescriptor<DCOMP._ISelfInfo>(DCOMP.SelfInfo.Default());
    public static Dafny.TypeDescriptor<DCOMP._ISelfInfo> _TypeDescriptor() {
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
  }
  public class SelfInfo_NoSelf : SelfInfo {
    public SelfInfo_NoSelf() : base() {
    }
    public override _ISelfInfo DowncastClone() {
      if (this is _ISelfInfo dt) { return dt; }
      return new SelfInfo_NoSelf();
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.SelfInfo_NoSelf;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.SelfInfo.NoSelf";
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
      var oth = other as DCOMP.SelfInfo_ThisTyped;
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
      string s = "DafnyToRustCompiler.SelfInfo.ThisTyped";
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
    Dafny.ISequence<Dafny.Rune> dtor_enclosingModule { get; }
    Dafny.ISequence<Dafny.Rune> dtor_reason { get; }
    _IExternAttribute DowncastClone();
  }
  public abstract class ExternAttribute : _IExternAttribute {
    public ExternAttribute() {
    }
    private static readonly DCOMP._IExternAttribute theDefault = create_NoExtern();
    public static DCOMP._IExternAttribute Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<DCOMP._IExternAttribute> _TYPE = new Dafny.TypeDescriptor<DCOMP._IExternAttribute>(DCOMP.ExternAttribute.Default());
    public static Dafny.TypeDescriptor<DCOMP._IExternAttribute> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IExternAttribute create_NoExtern() {
      return new ExternAttribute_NoExtern();
    }
    public static _IExternAttribute create_SimpleExtern(Dafny.ISequence<Dafny.Rune> overrideName) {
      return new ExternAttribute_SimpleExtern(overrideName);
    }
    public static _IExternAttribute create_AdvancedExtern(Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<Dafny.Rune> overrideName) {
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
    public Dafny.ISequence<Dafny.Rune> dtor_enclosingModule {
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
      var oth = other as DCOMP.ExternAttribute_NoExtern;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.ExternAttribute.NoExtern";
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
      var oth = other as DCOMP.ExternAttribute_SimpleExtern;
      return oth != null && object.Equals(this._overrideName, oth._overrideName);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._overrideName));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.ExternAttribute.SimpleExtern";
      s += "(";
      s += this._overrideName.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }
  public class ExternAttribute_AdvancedExtern : ExternAttribute {
    public readonly Dafny.ISequence<Dafny.Rune> _enclosingModule;
    public readonly Dafny.ISequence<Dafny.Rune> _overrideName;
    public ExternAttribute_AdvancedExtern(Dafny.ISequence<Dafny.Rune> enclosingModule, Dafny.ISequence<Dafny.Rune> overrideName) : base() {
      this._enclosingModule = enclosingModule;
      this._overrideName = overrideName;
    }
    public override _IExternAttribute DowncastClone() {
      if (this is _IExternAttribute dt) { return dt; }
      return new ExternAttribute_AdvancedExtern(_enclosingModule, _overrideName);
    }
    public override bool Equals(object other) {
      var oth = other as DCOMP.ExternAttribute_AdvancedExtern;
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
      string s = "DafnyToRustCompiler.ExternAttribute.AdvancedExtern";
      s += "(";
      s += this._enclosingModule.ToVerbatimString(true);
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
      var oth = other as DCOMP.ExternAttribute_UnsupportedExtern;
      return oth != null && object.Equals(this._reason, oth._reason);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._reason));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.ExternAttribute.UnsupportedExtern";
      s += "(";
      s += this._reason.ToVerbatimString(true);
      s += ")";
      return s;
    }
  }

  public partial class COMP {
    public COMP() {
      this.error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.Default();
      this._UnicodeChars = false;
      this._ObjectType = DCOMP.ObjectType.Default();
    }
    public RAST._IType Object(RAST._IType underlying) {
      if (((this).ObjectType).is_RawPointers) {
        return RAST.Type.create_PointerMut(underlying);
      } else {
        return RAST.__default.ObjectType(underlying);
      }
    }
    public Dafny.ISequence<Dafny.Rune> UnreachablePanicIfVerified(Dafny.ISequence<Dafny.Rune> optText) {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe { ::std::hint::unreachable_unchecked() }");
      } else if ((optText).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()");
      } else {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\""), optText), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")"));
      }
    }
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> error {get; set;}
    public void __ctor(bool unicodeChars, DCOMP._IObjectType objectType)
    {
      (this)._UnicodeChars = unicodeChars;
      (this)._ObjectType = objectType;
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      if ((objectType).is_RawPointers) {
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Raw pointers need to be wrapped in a newtype so that their equality has the semantics of Dafny (e.g. a class pointer and a trait pointer are equal), not Rust."));
      }
    }
    public RAST._IMod GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      RAST._IMod s = RAST.Mod.Default();
      Dafny.ISequence<Dafny.Rune> _1158_modName;
      _1158_modName = DCOMP.__default.escapeType((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1158_modName);
      } else {
        DCOMP._IExternAttribute _1159_optExtern;
        _1159_optExtern = DCOMP.__default.ExtractExternMod(mod);
        Dafny.ISequence<RAST._IModDecl> _1160_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1160_body = _out15;
        if ((_1159_optExtern).is_SimpleExtern) {
          if ((mod).dtor_requiresExterns) {
            _1160_body = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"))).MSel(DCOMP.COMP.DAFNY__EXTERN__MODULE)).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1159_optExtern).dtor_overrideName))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))), _1160_body);
          }
        } else if ((_1159_optExtern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Externs on modules can only have 1 string argument"));
        } else if ((_1159_optExtern).is_UnsupportedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some((_1159_optExtern).dtor_reason);
        }
        s = RAST.Mod.create_Mod(_1158_modName, _1160_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi6 = new BigInteger((body).Count);
      for (BigInteger _1161_i = BigInteger.Zero; _1161_i < _hi6; _1161_i++) {
        Dafny.ISequence<RAST._IModDecl> _1162_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source55 = (body).Select(_1161_i);
        bool unmatched55 = true;
        if (unmatched55) {
          if (_source55.is_Module) {
            DAST._IModule _1163_m = _source55.dtor_Module_a0;
            unmatched55 = false;
            RAST._IMod _1164_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1163_m, containingPath);
            _1164_mm = _out16;
            _1162_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1164_mm));
          }
        }
        if (unmatched55) {
          if (_source55.is_Class) {
            DAST._IClass _1165_c = _source55.dtor_Class_a0;
            unmatched55 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1165_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1165_c).dtor_name)));
            _1162_generated = _out17;
          }
        }
        if (unmatched55) {
          if (_source55.is_Trait) {
            DAST._ITrait _1166_t = _source55.dtor_Trait_a0;
            unmatched55 = false;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenTrait(_1166_t, containingPath);
            _1162_generated = _out18;
          }
        }
        if (unmatched55) {
          if (_source55.is_Newtype) {
            DAST._INewtype _1167_n = _source55.dtor_Newtype_a0;
            unmatched55 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1167_n);
            _1162_generated = _out19;
          }
        }
        if (unmatched55) {
          if (_source55.is_SynonymType) {
            DAST._ISynonymType _1168_s = _source55.dtor_SynonymType_a0;
            unmatched55 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1168_s);
            _1162_generated = _out20;
          }
        }
        if (unmatched55) {
          DAST._IDatatype _1169_d = _source55.dtor_Datatype_a0;
          unmatched55 = false;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1169_d);
          _1162_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1162_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1170_genTpConstraint;
      _1170_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1170_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1170_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeType(((tp).dtor_name)), _1170_genTpConstraint);
    }
    public void GenTypeParameters(Dafny.ISequence<DAST._ITypeArgDecl> @params, out Dafny.ISequence<DAST._IType> typeParamsSeq, out Dafny.ISequence<RAST._IType> typeParams, out Dafny.ISequence<RAST._ITypeParamDecl> constrainedTypeParams, out Dafny.ISequence<Dafny.Rune> whereConstraints)
    {
      typeParamsSeq = Dafny.Sequence<DAST._IType>.Empty;
      typeParams = Dafny.Sequence<RAST._IType>.Empty;
      constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Empty;
      whereConstraints = Dafny.Sequence<Dafny.Rune>.Empty;
      typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      whereConstraints = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
      if ((new BigInteger((@params).Count)).Sign == 1) {
        BigInteger _hi7 = new BigInteger((@params).Count);
        for (BigInteger _1171_tpI = BigInteger.Zero; _1171_tpI < _hi7; _1171_tpI++) {
          DAST._ITypeArgDecl _1172_tp;
          _1172_tp = (@params).Select(_1171_tpI);
          DAST._IType _1173_typeArg;
          RAST._ITypeParamDecl _1174_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1172_tp, out _out22, out _out23);
          _1173_typeArg = _out22;
          _1174_typeParam = _out23;
          RAST._IType _1175_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1173_typeArg, DCOMP.GenTypeContext.@default());
          _1175_rType = _out24;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1173_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1175_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1174_typeParam));
        }
      }
    }
    public bool IsSameResolvedTypeAnyArgs(DAST._IResolvedType r1, DAST._IResolvedType r2)
    {
      return (((r1).dtor_path).Equals((r2).dtor_path)) && (object.Equals((r1).dtor_kind, (r2).dtor_kind));
    }
    public bool IsSameResolvedType(DAST._IResolvedType r1, DAST._IResolvedType r2)
    {
      return ((this).IsSameResolvedTypeAnyArgs(r1, r2)) && (((r1).dtor_typeArgs).Equals((r2).dtor_typeArgs));
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1176_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1177_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1178_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1179_whereConstraints;
      Dafny.ISequence<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1176_typeParamsSeq = _out25;
      _1177_rTypeParams = _out26;
      _1178_rTypeParamsDecls = _out27;
      _1179_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1180_constrainedTypeParams;
      _1180_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1178_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1181_fields;
      _1181_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1182_fieldInits;
      _1182_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi8 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1183_fieldI = BigInteger.Zero; _1183_fieldI < _hi8; _1183_fieldI++) {
        DAST._IField _1184_field;
        _1184_field = ((c).dtor_fields).Select(_1183_fieldI);
        RAST._IType _1185_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1184_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1185_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1186_fieldRustName;
        _1186_fieldRustName = DCOMP.__default.escapeName(((_1184_field).dtor_formal).dtor_name);
        _1181_fields = Dafny.Sequence<RAST._IField>.Concat(_1181_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1186_fieldRustName, _1185_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source56 = (_1184_field).dtor_defaultValue;
        bool unmatched56 = true;
        if (unmatched56) {
          if (_source56.is_Some) {
            DAST._IExpression _1187_e = _source56.dtor_value;
            unmatched56 = false;
            {
              RAST._IExpr _1188_expr;
              DCOMP._IOwnership _1189___v49;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1190___v50;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1187_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1188_expr = _out30;
              _1189___v49 = _out31;
              _1190___v50 = _out32;
              _1182_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1182_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1186_fieldRustName, _1188_expr)));
            }
          }
        }
        if (unmatched56) {
          unmatched56 = false;
          {
            RAST._IExpr _1191_default;
            _1191_default = RAST.__default.std__Default__default;
            if ((_1185_fieldType).IsObjectOrPointer()) {
              _1191_default = (_1185_fieldType).ToNullExpr();
            }
            _1182_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1182_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1186_fieldRustName, _1191_default)));
          }
        }
      }
      BigInteger _hi9 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1192_typeParamI = BigInteger.Zero; _1192_typeParamI < _hi9; _1192_typeParamI++) {
        DAST._IType _1193_typeArg;
        RAST._ITypeParamDecl _1194_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1192_typeParamI), out _out33, out _out34);
        _1193_typeArg = _out33;
        _1194_typeParam = _out34;
        RAST._IType _1195_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1193_typeArg, DCOMP.GenTypeContext.@default());
        _1195_rTypeArg = _out35;
        _1181_fields = Dafny.Sequence<RAST._IField>.Concat(_1181_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1192_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1195_rTypeArg))))));
        _1182_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1182_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1192_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      DCOMP._IExternAttribute _1196_extern;
      _1196_extern = DCOMP.__default.ExtractExtern((c).dtor_attributes, (c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _1197_className = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((_1196_extern).is_SimpleExtern) {
        _1197_className = (_1196_extern).dtor_overrideName;
      } else {
        _1197_className = DCOMP.__default.escapeType((c).dtor_name);
        if ((_1196_extern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multi-argument externs not supported for classes yet"));
        }
      }
      RAST._IStruct _1198_struct;
      _1198_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1197_className, _1178_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1181_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_1196_extern).is_NoExtern) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1198_struct)));
      }
      Dafny.ISequence<RAST._IImplMember> _1199_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1200_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1176_typeParamsSeq, out _out36, out _out37);
      _1199_implBody = _out36;
      _1200_traitBodies = _out37;
      if (((_1196_extern).is_NoExtern) && (!(_1197_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default")))) {
        _1199_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.Type.create_SelfOwned())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel((this).allocate)).ApplyType1(RAST.Type.create_SelfOwned())).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1199_implBody);
      }
      RAST._IType _1201_selfTypeForImpl = RAST.Type.Default();
      if (((_1196_extern).is_NoExtern) || ((_1196_extern).is_UnsupportedExtern)) {
        _1201_selfTypeForImpl = RAST.Type.create_TIdentifier(_1197_className);
      } else if ((_1196_extern).is_AdvancedExtern) {
        _1201_selfTypeForImpl = ((RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"))).MSel((_1196_extern).dtor_enclosingModule)).MSel((_1196_extern).dtor_overrideName);
      } else if ((_1196_extern).is_SimpleExtern) {
        _1201_selfTypeForImpl = RAST.Type.create_TIdentifier((_1196_extern).dtor_overrideName);
      }
      if ((new BigInteger((_1199_implBody).Count)).Sign == 1) {
        RAST._IImpl _1202_i;
        _1202_i = RAST.Impl.create_Impl(_1178_rTypeParamsDecls, RAST.Type.create_TypeApp(_1201_selfTypeForImpl, _1177_rTypeParams), _1179_whereConstraints, _1199_implBody);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1202_i)));
      }
      RAST._IType _1203_genSelfPath;
      RAST._IType _out38;
      _out38 = DCOMP.COMP.GenPath(path);
      _1203_genSelfPath = _out38;
      if (!(_1197_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1178_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"))))), RAST.Type.create_TypeApp(_1203_genSelfPath, _1177_rTypeParams), _1179_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any")))))))))));
      }
      Dafny.ISequence<DAST._IType> _1204_superClasses;
      _1204_superClasses = (((_1197_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) ? (Dafny.Sequence<DAST._IType>.FromElements()) : ((c).dtor_superClasses));
      BigInteger _hi10 = new BigInteger((_1204_superClasses).Count);
      for (BigInteger _1205_i = BigInteger.Zero; _1205_i < _hi10; _1205_i++) {
        DAST._IType _1206_superClass;
        _1206_superClass = (_1204_superClasses).Select(_1205_i);
        DAST._IType _source57 = _1206_superClass;
        bool unmatched57 = true;
        if (unmatched57) {
          if (_source57.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source57.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1207_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1208_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1209_properMethods = resolved0.dtor_properMethods;
              unmatched57 = false;
              {
                RAST._IType _1210_pathStr;
                RAST._IType _out39;
                _out39 = DCOMP.COMP.GenPath(_1207_traitPath);
                _1210_pathStr = _out39;
                Dafny.ISequence<RAST._IType> _1211_typeArgs;
                Dafny.ISequence<RAST._IType> _out40;
                _out40 = (this).GenTypeArgs(_1208_typeArgs, DCOMP.GenTypeContext.@default());
                _1211_typeArgs = _out40;
                Dafny.ISequence<RAST._IImplMember> _1212_body;
                _1212_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1200_traitBodies).Contains(_1207_traitPath)) {
                  _1212_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1200_traitBodies,_1207_traitPath);
                }
                RAST._IType _1213_traitType;
                _1213_traitType = RAST.Type.create_TypeApp(_1210_pathStr, _1211_typeArgs);
                if (!((_1196_extern).is_NoExtern)) {
                  if (((new BigInteger((_1212_body).Count)).Sign == 0) && ((new BigInteger((_1209_properMethods).Count)).Sign != 0)) {
                    goto continue_0;
                  }
                  if ((new BigInteger((_1212_body).Count)) != (new BigInteger((_1209_properMethods).Count))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: In the class "), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(path, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1214_s) => {
  return ((_1214_s));
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", some proper methods of ")), (_1213_traitType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" are marked {:extern} and some are not.")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" For the Rust compiler, please make all methods (")), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_1209_properMethods, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1215_s) => {
  return ((_1215_s));
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")  bodiless and mark as {:extern} and implement them in a Rust file, ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("or mark none of them as {:extern} and implement them in Dafny. ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.")));
                  }
                }
                RAST._IModDecl _1216_x;
                _1216_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1178_rTypeParamsDecls, _1213_traitType, RAST.Type.create_TypeApp(_1203_genSelfPath, _1177_rTypeParams), _1179_whereConstraints, _1212_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1216_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1178_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1213_traitType))), RAST.Type.create_TypeApp(_1203_genSelfPath, _1177_rTypeParams), _1179_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1213_traitType)))))))));
              }
            }
          }
        }
        if (unmatched57) {
          unmatched57 = false;
        }
      continue_0: ;
      }
    after_0: ;
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1217_typeParamsSeq;
      _1217_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1218_typeParamDecls;
      _1218_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1219_typeParams;
      _1219_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi11 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1220_tpI = BigInteger.Zero; _1220_tpI < _hi11; _1220_tpI++) {
          DAST._ITypeArgDecl _1221_tp;
          _1221_tp = ((t).dtor_typeParams).Select(_1220_tpI);
          DAST._IType _1222_typeArg;
          RAST._ITypeParamDecl _1223_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1221_tp, out _out41, out _out42);
          _1222_typeArg = _out41;
          _1223_typeParamDecl = _out42;
          _1217_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1217_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1222_typeArg));
          _1218_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1218_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1223_typeParamDecl));
          RAST._IType _1224_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1222_typeArg, DCOMP.GenTypeContext.@default());
          _1224_typeParam = _out43;
          _1219_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1219_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1224_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1225_fullPath;
      _1225_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1226_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1227___v54;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1225_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1217_typeParamsSeq, out _out44, out _out45);
      _1226_implBody = _out44;
      _1227___v54 = _out45;
      Dafny.ISequence<RAST._IType> _1228_parents;
      _1228_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi12 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1229_i = BigInteger.Zero; _1229_i < _hi12; _1229_i++) {
        RAST._IType _1230_tpe;
        RAST._IType _out46;
        _out46 = (this).GenType(((t).dtor_parents).Select(_1229_i), DCOMP.GenTypeContext.ForTraitParents());
        _1230_tpe = _out46;
        _1228_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1228_parents, Dafny.Sequence<RAST._IType>.FromElements(_1230_tpe)), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply1(RAST.Type.create_DynType(_1230_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1218_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeType((t).dtor_name)), _1219_typeParams), _1228_parents, _1226_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1231_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1232_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1233_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1234_whereConstraints;
      Dafny.ISequence<DAST._IType> _out47;
      Dafny.ISequence<RAST._IType> _out48;
      Dafny.ISequence<RAST._ITypeParamDecl> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1231_typeParamsSeq = _out47;
      _1232_rTypeParams = _out48;
      _1233_rTypeParamsDecls = _out49;
      _1234_whereConstraints = _out50;
      Dafny.ISequence<Dafny.Rune> _1235_constrainedTypeParams;
      _1235_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1233_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1236_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source58 = DCOMP.COMP.NewtypeRangeToRustType((c).dtor_range);
      bool unmatched58 = true;
      if (unmatched58) {
        if (_source58.is_Some) {
          RAST._IType _1237_v = _source58.dtor_value;
          unmatched58 = false;
          _1236_underlyingType = _1237_v;
        }
      }
      if (unmatched58) {
        unmatched58 = false;
        RAST._IType _out51;
        _out51 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1236_underlyingType = _out51;
      }
      DAST._IType _1238_resultingType;
      _1238_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1239_newtypeName;
      _1239_newtypeName = DCOMP.__default.escapeType((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1239_newtypeName, _1233_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1236_underlyingType))))));
      RAST._IExpr _1240_fnBody;
      _1240_fnBody = RAST.Expr.create_Identifier(_1239_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source59 = (c).dtor_witnessExpr;
      bool unmatched59 = true;
      if (unmatched59) {
        if (_source59.is_Some) {
          DAST._IExpression _1241_e = _source59.dtor_value;
          unmatched59 = false;
          {
            DAST._IExpression _1242_e;
            _1242_e = ((object.Equals((c).dtor_base, _1238_resultingType)) ? (_1241_e) : (DAST.Expression.create_Convert(_1241_e, (c).dtor_base, _1238_resultingType)));
            RAST._IExpr _1243_eStr;
            DCOMP._IOwnership _1244___v55;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1245___v56;
            RAST._IExpr _out52;
            DCOMP._IOwnership _out53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out54;
            (this).GenExpr(_1242_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out52, out _out53, out _out54);
            _1243_eStr = _out52;
            _1244___v55 = _out53;
            _1245___v56 = _out54;
            _1240_fnBody = (_1240_fnBody).Apply1(_1243_eStr);
          }
        }
      }
      if (unmatched59) {
        unmatched59 = false;
        {
          _1240_fnBody = (_1240_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1246_body;
      _1246_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1240_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source60 = (c).dtor_constraint;
      bool unmatched60 = true;
      if (unmatched60) {
        if (_source60.is_None) {
          unmatched60 = false;
        }
      }
      if (unmatched60) {
        DAST._INewtypeConstraint value8 = _source60.dtor_value;
        DAST._IFormal _1247_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1248_constraintStmts = value8.dtor_constraintStmts;
        unmatched60 = false;
        RAST._IExpr _1249_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1250___v57;
        DCOMP._IEnvironment _1251_newEnv;
        RAST._IExpr _out55;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out56;
        DCOMP._IEnvironment _out57;
        (this).GenStmts(_1248_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out55, out _out56, out _out57);
        _1249_rStmts = _out55;
        _1250___v57 = _out56;
        _1251_newEnv = _out57;
        Dafny.ISequence<RAST._IFormal> _1252_rFormals;
        Dafny.ISequence<RAST._IFormal> _out58;
        _out58 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1247_formal), false);
        _1252_rFormals = _out58;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1233_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1239_newtypeName), _1232_rTypeParams), _1234_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1252_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1249_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1233_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1239_newtypeName), _1232_rTypeParams), _1234_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1246_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1233_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1239_newtypeName), _1232_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1233_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1239_newtypeName), _1232_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1236_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1253_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1254_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1255_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1256_whereConstraints;
      Dafny.ISequence<DAST._IType> _out59;
      Dafny.ISequence<RAST._IType> _out60;
      Dafny.ISequence<RAST._ITypeParamDecl> _out61;
      Dafny.ISequence<Dafny.Rune> _out62;
      (this).GenTypeParameters((c).dtor_typeParams, out _out59, out _out60, out _out61, out _out62);
      _1253_typeParamsSeq = _out59;
      _1254_rTypeParams = _out60;
      _1255_rTypeParamsDecls = _out61;
      _1256_whereConstraints = _out62;
      Dafny.ISequence<Dafny.Rune> _1257_synonymTypeName;
      _1257_synonymTypeName = DCOMP.__default.escapeType((c).dtor_name);
      RAST._IType _1258_resultingType;
      RAST._IType _out63;
      _out63 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1258_resultingType = _out63;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1257_synonymTypeName, _1255_rTypeParamsDecls, _1258_resultingType)));
      Dafny.ISequence<RAST._ITypeParamDecl> _1259_defaultConstrainedTypeParams;
      _1259_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Std.Wrappers._IOption<DAST._IExpression> _source61 = (c).dtor_witnessExpr;
      bool unmatched61 = true;
      if (unmatched61) {
        if (_source61.is_Some) {
          DAST._IExpression _1260_e = _source61.dtor_value;
          unmatched61 = false;
          {
            RAST._IExpr _1261_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1262___v58;
            DCOMP._IEnvironment _1263_newEnv;
            RAST._IExpr _out64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out65;
            DCOMP._IEnvironment _out66;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out64, out _out65, out _out66);
            _1261_rStmts = _out64;
            _1262___v58 = _out65;
            _1263_newEnv = _out66;
            RAST._IExpr _1264_rExpr;
            DCOMP._IOwnership _1265___v59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1266___v60;
            RAST._IExpr _out67;
            DCOMP._IOwnership _out68;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out69;
            (this).GenExpr(_1260_e, DCOMP.SelfInfo.create_NoSelf(), _1263_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out67, out _out68, out _out69);
            _1264_rExpr = _out67;
            _1265___v59 = _out68;
            _1266___v60 = _out69;
            Dafny.ISequence<Dafny.Rune> _1267_constantName;
            _1267_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1267_constantName, _1259_defaultConstrainedTypeParams, Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1258_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1261_rStmts).Then(_1264_rExpr)))))));
          }
        }
      }
      if (unmatched61) {
        unmatched61 = false;
      }
      return s;
    }
    public bool TypeIsEq(DAST._IType t) {
      DAST._IType _source62 = t;
      bool unmatched62 = true;
      if (unmatched62) {
        if (_source62.is_UserDefined) {
          unmatched62 = false;
          return true;
        }
      }
      if (unmatched62) {
        if (_source62.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1268_ts = _source62.dtor_Tuple_a0;
          unmatched62 = false;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1269_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1269_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1270_t = (DAST._IType)_forall_var_5;
            return !((_1269_ts).Contains(_1270_t)) || ((this).TypeIsEq(_1270_t));
          }))))(_1268_ts);
        }
      }
      if (unmatched62) {
        if (_source62.is_Array) {
          DAST._IType _1271_t = _source62.dtor_element;
          unmatched62 = false;
          return (this).TypeIsEq(_1271_t);
        }
      }
      if (unmatched62) {
        if (_source62.is_Seq) {
          DAST._IType _1272_t = _source62.dtor_element;
          unmatched62 = false;
          return (this).TypeIsEq(_1272_t);
        }
      }
      if (unmatched62) {
        if (_source62.is_Set) {
          DAST._IType _1273_t = _source62.dtor_element;
          unmatched62 = false;
          return (this).TypeIsEq(_1273_t);
        }
      }
      if (unmatched62) {
        if (_source62.is_Multiset) {
          DAST._IType _1274_t = _source62.dtor_element;
          unmatched62 = false;
          return (this).TypeIsEq(_1274_t);
        }
      }
      if (unmatched62) {
        if (_source62.is_Map) {
          DAST._IType _1275_k = _source62.dtor_key;
          DAST._IType _1276_v = _source62.dtor_value;
          unmatched62 = false;
          return ((this).TypeIsEq(_1275_k)) && ((this).TypeIsEq(_1276_v));
        }
      }
      if (unmatched62) {
        if (_source62.is_SetBuilder) {
          DAST._IType _1277_t = _source62.dtor_element;
          unmatched62 = false;
          return (this).TypeIsEq(_1277_t);
        }
      }
      if (unmatched62) {
        if (_source62.is_MapBuilder) {
          DAST._IType _1278_k = _source62.dtor_key;
          DAST._IType _1279_v = _source62.dtor_value;
          unmatched62 = false;
          return ((this).TypeIsEq(_1278_k)) && ((this).TypeIsEq(_1279_v));
        }
      }
      if (unmatched62) {
        if (_source62.is_Arrow) {
          unmatched62 = false;
          return false;
        }
      }
      if (unmatched62) {
        if (_source62.is_Primitive) {
          unmatched62 = false;
          return true;
        }
      }
      if (unmatched62) {
        if (_source62.is_Passthrough) {
          unmatched62 = false;
          return true;
        }
      }
      if (unmatched62) {
        if (_source62.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _1280_i = _source62.dtor_TypeArg_a0;
          unmatched62 = false;
          return true;
        }
      }
      if (unmatched62) {
        unmatched62 = false;
        return true;
      }
      throw new System.Exception("unexpected control point");
    }
    public bool DatatypeIsEq(DAST._IDatatype c) {
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1281_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1281_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1282_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1282_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1283_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1281_c).dtor_ctors).Contains(_1282_ctor)) && (((_1282_ctor).dtor_args).Contains(_1283_arg))) || ((this).TypeIsEq(((_1283_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1284_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1285_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1286_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1287_whereConstraints;
      Dafny.ISequence<DAST._IType> _out70;
      Dafny.ISequence<RAST._IType> _out71;
      Dafny.ISequence<RAST._ITypeParamDecl> _out72;
      Dafny.ISequence<Dafny.Rune> _out73;
      (this).GenTypeParameters((c).dtor_typeParams, out _out70, out _out71, out _out72, out _out73);
      _1284_typeParamsSeq = _out70;
      _1285_rTypeParams = _out71;
      _1286_rTypeParamsDecls = _out72;
      _1287_whereConstraints = _out73;
      Dafny.ISequence<Dafny.Rune> _1288_datatypeName;
      _1288_datatypeName = DCOMP.__default.escapeType((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1289_ctors;
      _1289_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _1290_variances;
      _1290_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_1291_typeParamDecl) => {
        return (_1291_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1292_i = BigInteger.Zero; _1292_i < _hi13; _1292_i++) {
        DAST._IDatatypeCtor _1293_ctor;
        _1293_ctor = ((c).dtor_ctors).Select(_1292_i);
        Dafny.ISequence<RAST._IField> _1294_ctorArgs;
        _1294_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1295_isNumeric;
        _1295_isNumeric = false;
        BigInteger _hi14 = new BigInteger(((_1293_ctor).dtor_args).Count);
        for (BigInteger _1296_j = BigInteger.Zero; _1296_j < _hi14; _1296_j++) {
          DAST._IDatatypeDtor _1297_dtor;
          _1297_dtor = ((_1293_ctor).dtor_args).Select(_1296_j);
          RAST._IType _1298_formalType;
          RAST._IType _out74;
          _out74 = (this).GenType(((_1297_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1298_formalType = _out74;
          Dafny.ISequence<Dafny.Rune> _1299_formalName;
          _1299_formalName = DCOMP.__default.escapeName(((_1297_dtor).dtor_formal).dtor_name);
          if (((_1296_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1299_formalName))) {
            _1295_isNumeric = true;
          }
          if ((((_1296_j).Sign != 0) && (_1295_isNumeric)) && (!(Std.Strings.__default.OfNat(_1296_j)).Equals(_1299_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1299_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1296_j)));
            _1295_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1294_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1294_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1299_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1298_formalType))))));
          } else {
            _1294_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1294_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1299_formalName, _1298_formalType))));
          }
        }
        RAST._IFields _1300_namedFields;
        _1300_namedFields = RAST.Fields.create_NamedFields(_1294_ctorArgs);
        if (_1295_isNumeric) {
          _1300_namedFields = (_1300_namedFields).ToNamelessFields();
        }
        _1289_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1289_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1293_ctor).dtor_name), _1300_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1301_selfPath;
      _1301_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1302_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1303_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out75;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out76;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1301_selfPath, _1284_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1290_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1284_typeParamsSeq, out _out75, out _out76);
      _1302_implBodyRaw = _out75;
      _1303_traitBodies = _out76;
      Dafny.ISequence<RAST._IImplMember> _1304_implBody;
      _1304_implBody = _1302_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1305_emittedFields;
      _1305_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi15 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1306_i = BigInteger.Zero; _1306_i < _hi15; _1306_i++) {
        DAST._IDatatypeCtor _1307_ctor;
        _1307_ctor = ((c).dtor_ctors).Select(_1306_i);
        BigInteger _hi16 = new BigInteger(((_1307_ctor).dtor_args).Count);
        for (BigInteger _1308_j = BigInteger.Zero; _1308_j < _hi16; _1308_j++) {
          DAST._IDatatypeDtor _1309_dtor;
          _1309_dtor = ((_1307_ctor).dtor_args).Select(_1308_j);
          Dafny.ISequence<Dafny.Rune> _1310_callName;
          _1310_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1309_dtor).dtor_callName, DCOMP.__default.escapeName(((_1309_dtor).dtor_formal).dtor_name));
          if (!((_1305_emittedFields).Contains(_1310_callName))) {
            _1305_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1305_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1310_callName));
            RAST._IType _1311_formalType;
            RAST._IType _out77;
            _out77 = (this).GenType(((_1309_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1311_formalType = _out77;
            Dafny.ISequence<RAST._IMatchCase> _1312_cases;
            _1312_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi17 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1313_k = BigInteger.Zero; _1313_k < _hi17; _1313_k++) {
              DAST._IDatatypeCtor _1314_ctor2;
              _1314_ctor2 = ((c).dtor_ctors).Select(_1313_k);
              Dafny.ISequence<Dafny.Rune> _1315_pattern;
              _1315_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1288_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1314_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1316_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1317_hasMatchingField;
              _1317_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1318_patternInner;
              _1318_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1319_isNumeric;
              _1319_isNumeric = false;
              BigInteger _hi18 = new BigInteger(((_1314_ctor2).dtor_args).Count);
              for (BigInteger _1320_l = BigInteger.Zero; _1320_l < _hi18; _1320_l++) {
                DAST._IDatatypeDtor _1321_dtor2;
                _1321_dtor2 = ((_1314_ctor2).dtor_args).Select(_1320_l);
                Dafny.ISequence<Dafny.Rune> _1322_patternName;
                _1322_patternName = DCOMP.__default.escapeDtor(((_1321_dtor2).dtor_formal).dtor_name);
                Dafny.ISequence<Dafny.Rune> _1323_varName;
                _1323_varName = DCOMP.__default.escapeVar(((_1321_dtor2).dtor_formal).dtor_name);
                if (((_1320_l).Sign == 0) && ((_1322_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1319_isNumeric = true;
                }
                if (_1319_isNumeric) {
                  _1322_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1321_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1320_l)));
                  _1323_varName = _1322_patternName;
                }
                if (object.Equals(((_1309_dtor).dtor_formal).dtor_name, ((_1321_dtor2).dtor_formal).dtor_name)) {
                  _1317_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1323_varName);
                }
                _1318_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1318_patternInner, _1322_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1319_isNumeric) {
                _1315_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1315_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1318_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1315_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1315_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1318_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1317_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1316_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1317_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1316_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1317_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1316_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _1324_ctorMatch;
              _1324_ctorMatch = RAST.MatchCase.create(_1315_pattern, RAST.Expr.create_RawExpr(_1316_rhs));
              _1312_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1312_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1324_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1312_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1312_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1288_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _1325_methodBody;
            _1325_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1312_cases);
            _1304_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1304_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1310_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1311_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1325_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1326_coerceTypes;
      _1326_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1327_rCoerceTypeParams;
      _1327_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1328_coerceArguments;
      _1328_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1329_coerceMap;
      _1329_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1330_rCoerceMap;
      _1330_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1331_coerceMapToArg;
      _1331_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1332_types;
        _1332_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi19 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1333_typeI = BigInteger.Zero; _1333_typeI < _hi19; _1333_typeI++) {
          DAST._ITypeArgDecl _1334_typeParam;
          _1334_typeParam = ((c).dtor_typeParams).Select(_1333_typeI);
          DAST._IType _1335_typeArg;
          RAST._ITypeParamDecl _1336_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(_1334_typeParam, out _out78, out _out79);
          _1335_typeArg = _out78;
          _1336_rTypeParamDecl = _out79;
          RAST._IType _1337_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1335_typeArg, DCOMP.GenTypeContext.@default());
          _1337_rTypeArg = _out80;
          _1332_types = Dafny.Sequence<RAST._IType>.Concat(_1332_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1337_rTypeArg))));
          if (((_1333_typeI) < (new BigInteger((_1290_variances).Count))) && (((_1290_variances).Select(_1333_typeI)).is_Nonvariant)) {
            _1326_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1326_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1337_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1338_coerceTypeParam;
          _1338_coerceTypeParam = Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_1334_typeParam, _pat_let9_0 => Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_pat_let9_0, _1339_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1333_typeI)), _pat_let10_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(_pat_let10_0, _1340_dt__update_hname_h0 => DAST.TypeArgDecl.create(_1340_dt__update_hname_h0, (_1339_dt__update__tmp_h0).dtor_bounds, (_1339_dt__update__tmp_h0).dtor_variance)))));
          DAST._IType _1341_coerceTypeArg;
          RAST._ITypeParamDecl _1342_rCoerceTypeParamDecl;
          DAST._IType _out81;
          RAST._ITypeParamDecl _out82;
          (this).GenTypeParam(_1338_coerceTypeParam, out _out81, out _out82);
          _1341_coerceTypeArg = _out81;
          _1342_rCoerceTypeParamDecl = _out82;
          _1329_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1329_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1335_typeArg, _1341_coerceTypeArg)));
          RAST._IType _1343_rCoerceType;
          RAST._IType _out83;
          _out83 = (this).GenType(_1341_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1343_rCoerceType = _out83;
          _1330_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1330_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1337_rTypeArg, _1343_rCoerceType)));
          _1326_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1326_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1343_rCoerceType));
          _1327_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1327_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1342_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1344_coerceFormal;
          _1344_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1333_typeI));
          _1331_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1331_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1337_rTypeArg, _1343_rCoerceType), (RAST.Expr.create_Identifier(_1344_coerceFormal)).Clone())));
          _1328_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1328_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1344_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1337_rTypeArg), _1343_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        _1289_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1289_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1345_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1345_tpe);
})), _1332_types)))));
      }
      bool _1346_cIsEq;
      _1346_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1346_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1288_datatypeName, _1286_rTypeParamsDecls, _1289_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1286_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams), _1287_whereConstraints, _1304_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1347_printImplBodyCases;
      _1347_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1348_hashImplBodyCases;
      _1348_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1349_coerceImplBodyCases;
      _1349_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi20 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1350_i = BigInteger.Zero; _1350_i < _hi20; _1350_i++) {
        DAST._IDatatypeCtor _1351_ctor;
        _1351_ctor = ((c).dtor_ctors).Select(_1350_i);
        Dafny.ISequence<Dafny.Rune> _1352_ctorMatch;
        _1352_ctorMatch = DCOMP.__default.escapeName((_1351_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1353_modulePrefix;
        _1353_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1354_ctorName;
        _1354_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1353_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1351_ctor).dtor_name));
        if (((new BigInteger((_1354_ctorName).Count)) >= (new BigInteger(13))) && (((_1354_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1354_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1355_printRhs;
        _1355_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1354_ctorName), (((_1351_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1356_hashRhs;
        _1356_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1357_coerceRhsArgs;
        _1357_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1358_isNumeric;
        _1358_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1359_ctorMatchInner;
        _1359_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi21 = new BigInteger(((_1351_ctor).dtor_args).Count);
        for (BigInteger _1360_j = BigInteger.Zero; _1360_j < _hi21; _1360_j++) {
          DAST._IDatatypeDtor _1361_dtor;
          _1361_dtor = ((_1351_ctor).dtor_args).Select(_1360_j);
          Dafny.ISequence<Dafny.Rune> _1362_patternName;
          _1362_patternName = DCOMP.__default.escapeDtor(((_1361_dtor).dtor_formal).dtor_name);
          Dafny.ISequence<Dafny.Rune> _1363_fieldName;
          _1363_fieldName = DCOMP.__default.escapeVar(((_1361_dtor).dtor_formal).dtor_name);
          DAST._IType _1364_formalType;
          _1364_formalType = ((_1361_dtor).dtor_formal).dtor_typ;
          if (((_1360_j).Sign == 0) && ((_1363_fieldName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1358_isNumeric = true;
          }
          if (_1358_isNumeric) {
            _1363_fieldName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1361_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1360_j)));
          }
          _1356_hashRhs = (((_1364_formalType).is_Arrow) ? ((_1356_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))) : ((_1356_hashRhs).Then(((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1363_fieldName), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state")))))));
          _1359_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1359_ctorMatchInner, ((_1358_isNumeric) ? (_1363_fieldName) : (_1362_patternName))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1360_j).Sign == 1) {
            _1355_printRhs = (_1355_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1355_printRhs = (_1355_printRhs).Then(RAST.Expr.create_RawExpr((((_1364_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1363_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1365_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1366_formalTpe;
          RAST._IType _out84;
          _out84 = (this).GenType(_1364_formalType, DCOMP.GenTypeContext.@default());
          _1366_formalTpe = _out84;
          DAST._IType _1367_newFormalType;
          _1367_newFormalType = (_1364_formalType).Replace(_1329_coerceMap);
          RAST._IType _1368_newFormalTpe;
          _1368_newFormalTpe = (_1366_formalTpe).Replace(_1330_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1369_upcastConverter;
          _1369_upcastConverter = (this).UpcastConversionLambda(_1364_formalType, _1366_formalTpe, _1367_newFormalType, _1368_newFormalTpe, _1331_coerceMapToArg);
          if ((_1369_upcastConverter).is_Success) {
            RAST._IExpr _1370_coercionFunction;
            _1370_coercionFunction = (_1369_upcastConverter).dtor_value;
            _1365_coerceRhsArg = (_1370_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1362_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1360_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1288_datatypeName));
            _1365_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1357_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1357_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1362_patternName, _1365_coerceRhsArg)));
        }
        RAST._IExpr _1371_coerceRhs;
        _1371_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1288_datatypeName)).MSel(DCOMP.__default.escapeName((_1351_ctor).dtor_name)), _1357_coerceRhsArgs);
        if (_1358_isNumeric) {
          _1352_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1352_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1359_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1352_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1352_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1359_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1351_ctor).dtor_hasAnyArgs) {
          _1355_printRhs = (_1355_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1355_printRhs = (_1355_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1347_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1347_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1288_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1352_ctorMatch), RAST.Expr.create_Block(_1355_printRhs))));
        _1348_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1348_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1288_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1352_ctorMatch), RAST.Expr.create_Block(_1356_hashRhs))));
        _1349_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1349_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1288_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1352_ctorMatch), RAST.Expr.create_Block(_1371_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1372_extraCases;
        _1372_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1288_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _1347_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1347_printImplBodyCases, _1372_extraCases);
        _1348_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1348_hashImplBodyCases, _1372_extraCases);
        _1349_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1349_coerceImplBodyCases, _1372_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1373_defaultConstrainedTypeParams;
      _1373_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1286_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1374_rTypeParamsDeclsWithEq;
      _1374_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1286_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1375_rTypeParamsDeclsWithHash;
      _1375_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1286_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1376_printImplBody;
      _1376_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1347_printImplBodyCases);
      RAST._IExpr _1377_hashImplBody;
      _1377_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1348_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1286_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1286_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1376_printImplBody))))))));
      if ((new BigInteger((_1327_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1378_coerceImplBody;
        _1378_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1349_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1286_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1327_rCoerceTypeParams, _1328_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1326_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.Type.create_SelfOwned())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1326_coerceTypes)), _1378_coerceImplBody))))))))));
      }
      if (_1346_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1374_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1375_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1377_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1379_structName;
        _1379_structName = (RAST.Expr.create_Identifier(_1288_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1380_structAssignments;
        _1380_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi22 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1381_i = BigInteger.Zero; _1381_i < _hi22; _1381_i++) {
          DAST._IDatatypeDtor _1382_dtor;
          _1382_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1381_i);
          _1380_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1380_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1382_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1383_defaultConstrainedTypeParams;
        _1383_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1286_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1384_fullType;
        _1384_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams);
        if (_1346_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1383_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1384_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1384_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1379_structName, _1380_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1286_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1384_fullType), RAST.Type.create_Borrowed(_1384_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
      }
      return s;
    }
    public static RAST._IType GenPath(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IType r = RAST.Type.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        r = RAST.Type.create_SelfOwned();
        return r;
      } else {
        r = ((((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))) ? (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) : (((((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"))) ? (RAST.__default.dafny__runtime__type) : (RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"))))));
        BigInteger _hi23 = new BigInteger((p).Count);
        for (BigInteger _1385_i = BigInteger.Zero; _1385_i < _hi23; _1385_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1385_i))));
        }
      }
      return r;
    }
    public static RAST._IExpr GenPathExpr(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p, bool escape)
    {
      RAST._IExpr r = RAST.Expr.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        r = RAST.__default.self;
        return r;
      } else {
        r = ((((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))) ? (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) : (((((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"))) ? (RAST.__default.dafny__runtime) : (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"))))));
        BigInteger _hi24 = new BigInteger((p).Count);
        for (BigInteger _1386_i = BigInteger.Zero; _1386_i < _hi24; _1386_i++) {
          Dafny.ISequence<Dafny.Rune> _1387_id;
          _1387_id = ((p).Select(_1386_i));
          r = (r).MSel(((escape) ? (DCOMP.__default.escapeName(_1387_id)) : (DCOMP.__default.ReplaceDotByDoubleColon((_1387_id)))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi25 = new BigInteger((args).Count);
      for (BigInteger _1388_i = BigInteger.Zero; _1388_i < _hi25; _1388_i++) {
        RAST._IType _1389_genTp;
        RAST._IType _out85;
        _out85 = (this).GenType((args).Select(_1388_i), genTypeContext);
        _1389_genTp = _out85;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1389_genTp));
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, DCOMP._IGenTypeContext genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source63 = c;
      bool unmatched63 = true;
      if (unmatched63) {
        if (_source63.is_UserDefined) {
          DAST._IResolvedType _1390_resolved = _source63.dtor_resolved;
          unmatched63 = false;
          {
            RAST._IType _1391_t;
            RAST._IType _out86;
            _out86 = DCOMP.COMP.GenPath((_1390_resolved).dtor_path);
            _1391_t = _out86;
            Dafny.ISequence<RAST._IType> _1392_typeArgs;
            Dafny.ISequence<RAST._IType> _out87;
            _out87 = (this).GenTypeArgs((_1390_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _1393_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _1394_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1393_dt__update__tmp_h0).dtor_inBinding, (_1393_dt__update__tmp_h0).dtor_inFn, _1394_dt__update_hforTraitParents_h0))))));
            _1392_typeArgs = _out87;
            s = RAST.Type.create_TypeApp(_1391_t, _1392_typeArgs);
            DAST._IResolvedTypeBase _source64 = (_1390_resolved).dtor_kind;
            bool unmatched64 = true;
            if (unmatched64) {
              if (_source64.is_Class) {
                unmatched64 = false;
                {
                  s = (this).Object(s);
                }
              }
            }
            if (unmatched64) {
              if (_source64.is_Datatype) {
                unmatched64 = false;
                {
                  if ((this).IsRcWrapped((_1390_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched64) {
              if (_source64.is_Trait) {
                unmatched64 = false;
                {
                  if (((_1390_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched64) {
              DAST._IType _1395_base = _source64.dtor_baseType;
              DAST._INewtypeRange _1396_range = _source64.dtor_range;
              bool _1397_erased = _source64.dtor_erase;
              unmatched64 = false;
              {
                if (_1397_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source65 = DCOMP.COMP.NewtypeRangeToRustType(_1396_range);
                  bool unmatched65 = true;
                  if (unmatched65) {
                    if (_source65.is_Some) {
                      RAST._IType _1398_v = _source65.dtor_value;
                      unmatched65 = false;
                      s = _1398_v;
                    }
                  }
                  if (unmatched65) {
                    unmatched65 = false;
                    RAST._IType _1399_underlying;
                    RAST._IType _out88;
                    _out88 = (this).GenType(_1395_base, DCOMP.GenTypeContext.@default());
                    _1399_underlying = _out88;
                    s = RAST.Type.create_TSynonym(s, _1399_underlying);
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Object) {
          unmatched63 = false;
          {
            s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
            if (!((genTypeContext).dtor_forTraitParents)) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1400_types = _source63.dtor_Tuple_a0;
          unmatched63 = false;
          {
            Dafny.ISequence<RAST._IType> _1401_args;
            _1401_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1402_i;
            _1402_i = BigInteger.Zero;
            while ((_1402_i) < (new BigInteger((_1400_types).Count))) {
              RAST._IType _1403_generated;
              RAST._IType _out89;
              _out89 = (this).GenType((_1400_types).Select(_1402_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _1404_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _1405_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1404_dt__update__tmp_h1).dtor_inBinding, (_1404_dt__update__tmp_h1).dtor_inFn, _1405_dt__update_hforTraitParents_h1))))));
              _1403_generated = _out89;
              _1401_args = Dafny.Sequence<RAST._IType>.Concat(_1401_args, Dafny.Sequence<RAST._IType>.FromElements(_1403_generated));
              _1402_i = (_1402_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1400_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1401_args)) : (RAST.__default.SystemTupleType(_1401_args)));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Array) {
          DAST._IType _1406_element = _source63.dtor_element;
          BigInteger _1407_dims = _source63.dtor_dims;
          unmatched63 = false;
          {
            if ((_1407_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1408_elem;
              RAST._IType _out90;
              _out90 = (this).GenType(_1406_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _1409_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _1410_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1409_dt__update__tmp_h2).dtor_inBinding, (_1409_dt__update__tmp_h2).dtor_inFn, _1410_dt__update_hforTraitParents_h2))))));
              _1408_elem = _out90;
              if ((_1407_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1408_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1411_n;
                _1411_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1407_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1411_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1408_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Seq) {
          DAST._IType _1412_element = _source63.dtor_element;
          unmatched63 = false;
          {
            RAST._IType _1413_elem;
            RAST._IType _out91;
            _out91 = (this).GenType(_1412_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _1414_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _1415_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1414_dt__update__tmp_h3).dtor_inBinding, (_1414_dt__update__tmp_h3).dtor_inFn, _1415_dt__update_hforTraitParents_h3))))));
            _1413_elem = _out91;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1413_elem));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Set) {
          DAST._IType _1416_element = _source63.dtor_element;
          unmatched63 = false;
          {
            RAST._IType _1417_elem;
            RAST._IType _out92;
            _out92 = (this).GenType(_1416_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _1418_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _1419_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1418_dt__update__tmp_h4).dtor_inBinding, (_1418_dt__update__tmp_h4).dtor_inFn, _1419_dt__update_hforTraitParents_h4))))));
            _1417_elem = _out92;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1417_elem));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Multiset) {
          DAST._IType _1420_element = _source63.dtor_element;
          unmatched63 = false;
          {
            RAST._IType _1421_elem;
            RAST._IType _out93;
            _out93 = (this).GenType(_1420_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _1422_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _1423_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1422_dt__update__tmp_h5).dtor_inBinding, (_1422_dt__update__tmp_h5).dtor_inFn, _1423_dt__update_hforTraitParents_h5))))));
            _1421_elem = _out93;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1421_elem));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Map) {
          DAST._IType _1424_key = _source63.dtor_key;
          DAST._IType _1425_value = _source63.dtor_value;
          unmatched63 = false;
          {
            RAST._IType _1426_keyType;
            RAST._IType _out94;
            _out94 = (this).GenType(_1424_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _1427_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _1428_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1427_dt__update__tmp_h6).dtor_inBinding, (_1427_dt__update__tmp_h6).dtor_inFn, _1428_dt__update_hforTraitParents_h6))))));
            _1426_keyType = _out94;
            RAST._IType _1429_valueType;
            RAST._IType _out95;
            _out95 = (this).GenType(_1425_value, genTypeContext);
            _1429_valueType = _out95;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1426_keyType, _1429_valueType));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_MapBuilder) {
          DAST._IType _1430_key = _source63.dtor_key;
          DAST._IType _1431_value = _source63.dtor_value;
          unmatched63 = false;
          {
            RAST._IType _1432_keyType;
            RAST._IType _out96;
            _out96 = (this).GenType(_1430_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _1433_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _1434_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1433_dt__update__tmp_h7).dtor_inBinding, (_1433_dt__update__tmp_h7).dtor_inFn, _1434_dt__update_hforTraitParents_h7))))));
            _1432_keyType = _out96;
            RAST._IType _1435_valueType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1431_value, genTypeContext);
            _1435_valueType = _out97;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1432_keyType, _1435_valueType));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_SetBuilder) {
          DAST._IType _1436_elem = _source63.dtor_element;
          unmatched63 = false;
          {
            RAST._IType _1437_elemType;
            RAST._IType _out98;
            _out98 = (this).GenType(_1436_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _1438_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _1439_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1438_dt__update__tmp_h8).dtor_inBinding, (_1438_dt__update__tmp_h8).dtor_inFn, _1439_dt__update_hforTraitParents_h8))))));
            _1437_elemType = _out98;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1437_elemType));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1440_args = _source63.dtor_args;
          DAST._IType _1441_result = _source63.dtor_result;
          unmatched63 = false;
          {
            Dafny.ISequence<RAST._IType> _1442_argTypes;
            _1442_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1443_i;
            _1443_i = BigInteger.Zero;
            while ((_1443_i) < (new BigInteger((_1440_args).Count))) {
              RAST._IType _1444_generated;
              RAST._IType _out99;
              _out99 = (this).GenType((_1440_args).Select(_1443_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let29_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let29_0, _1445_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let30_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let30_0, _1446_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let31_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let31_0, _1447_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1445_dt__update__tmp_h9).dtor_inBinding, _1447_dt__update_hinFn_h0, _1446_dt__update_hforTraitParents_h9))))))));
              _1444_generated = _out99;
              _1442_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1442_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1444_generated)));
              _1443_i = (_1443_i) + (BigInteger.One);
            }
            RAST._IType _1448_resultType;
            RAST._IType _out100;
            _out100 = (this).GenType(_1441_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1448_resultType = _out100;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1442_argTypes, _1448_resultType)));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source63.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1449_name = _h90;
          unmatched63 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeType(_1449_name));
        }
      }
      if (unmatched63) {
        if (_source63.is_Primitive) {
          DAST._IPrimitive _1450_p = _source63.dtor_Primitive_a0;
          unmatched63 = false;
          {
            DAST._IPrimitive _source66 = _1450_p;
            bool unmatched66 = true;
            if (unmatched66) {
              if (_source66.is_Int) {
                unmatched66 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
              }
            }
            if (unmatched66) {
              if (_source66.is_Real) {
                unmatched66 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
              }
            }
            if (unmatched66) {
              if (_source66.is_String) {
                unmatched66 = false;
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
              }
            }
            if (unmatched66) {
              if (_source66.is_Bool) {
                unmatched66 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched66) {
              unmatched66 = false;
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          }
        }
      }
      if (unmatched63) {
        Dafny.ISequence<Dafny.Rune> _1451_v = _source63.dtor_Passthrough_a0;
        unmatched63 = false;
        s = RAST.__default.RawType(_1451_v);
      }
      return s;
    }
    public bool EnclosingIsTrait(DAST._IType tpe) {
      return ((tpe).is_UserDefined) && ((((tpe).dtor_resolved).dtor_kind).is_Trait);
    }
    public void GenClassImplBody(Dafny.ISequence<DAST._IMethod> body, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams, out Dafny.ISequence<RAST._IImplMember> s, out Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> traitBodies)
    {
      s = Dafny.Sequence<RAST._IImplMember>.Empty;
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Empty;
      s = Dafny.Sequence<RAST._IImplMember>.FromElements();
      traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements();
      BigInteger _hi26 = new BigInteger((body).Count);
      for (BigInteger _1452_i = BigInteger.Zero; _1452_i < _hi26; _1452_i++) {
        DAST._IMethod _source67 = (body).Select(_1452_i);
        bool unmatched67 = true;
        if (unmatched67) {
          DAST._IMethod _1453_m = _source67;
          unmatched67 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source68 = (_1453_m).dtor_overridingPath;
            bool unmatched68 = true;
            if (unmatched68) {
              if (_source68.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1454_p = _source68.dtor_value;
                unmatched68 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1455_existing;
                  _1455_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1454_p)) {
                    _1455_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1454_p);
                  }
                  if (((new BigInteger(((_1453_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1456_genMethod;
                  RAST._IImplMember _out101;
                  _out101 = (this).GenMethod(_1453_m, true, enclosingType, enclosingTypeParams);
                  _1456_genMethod = _out101;
                  _1455_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1455_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1456_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1454_p, _1455_existing)));
                }
              }
            }
            if (unmatched68) {
              unmatched68 = false;
              {
                RAST._IImplMember _1457_generated;
                RAST._IImplMember _out102;
                _out102 = (this).GenMethod(_1453_m, forTrait, enclosingType, enclosingTypeParams);
                _1457_generated = _out102;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1457_generated));
              }
            }
          }
        }
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params, bool forLambda)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _hi27 = new BigInteger((@params).Count);
      for (BigInteger _1458_i = BigInteger.Zero; _1458_i < _hi27; _1458_i++) {
        DAST._IFormal _1459_param;
        _1459_param = (@params).Select(_1458_i);
        RAST._IType _1460_paramType;
        RAST._IType _out103;
        _out103 = (this).GenType((_1459_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1460_paramType = _out103;
        if (((!((_1460_paramType).CanReadWithoutClone())) || (forLambda)) && (!((_1459_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1460_paramType = RAST.Type.create_Borrowed(_1460_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeVar((_1459_param).dtor_name), _1460_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1461_params;
      Dafny.ISequence<RAST._IFormal> _out104;
      _out104 = (this).GenParams((m).dtor_params, false);
      _1461_params = _out104;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1462_paramNames;
      _1462_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1463_paramTypes;
      _1463_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1464_paramI = BigInteger.Zero; _1464_paramI < _hi28; _1464_paramI++) {
        DAST._IFormal _1465_dafny__formal;
        _1465_dafny__formal = ((m).dtor_params).Select(_1464_paramI);
        RAST._IFormal _1466_formal;
        _1466_formal = (_1461_params).Select(_1464_paramI);
        Dafny.ISequence<Dafny.Rune> _1467_name;
        _1467_name = (_1466_formal).dtor_name;
        _1462_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1462_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1467_name));
        _1463_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1463_paramTypes, _1467_name, (_1466_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1468_fnName;
      _1468_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1469_selfIdent;
      _1469_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1470_selfId;
        _1470_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1470_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv142 = enclosingTypeParams;
        var _pat_let_tv143 = enclosingType;
        DAST._IType _1471_instanceType;
        _1471_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source69 = enclosingType;
          bool unmatched69 = true;
          if (unmatched69) {
            if (_source69.is_UserDefined) {
              DAST._IResolvedType _1472_r = _source69.dtor_resolved;
              unmatched69 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1472_r, _pat_let32_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let32_0, _1473_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv142, _pat_let33_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let33_0, _1474_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1473_dt__update__tmp_h0).dtor_path, _1474_dt__update_htypeArgs_h0, (_1473_dt__update__tmp_h0).dtor_kind, (_1473_dt__update__tmp_h0).dtor_attributes, (_1473_dt__update__tmp_h0).dtor_properMethods, (_1473_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched69) {
            unmatched69 = false;
            return _pat_let_tv143;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1475_selfFormal;
          _1475_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1461_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1475_selfFormal), _1461_params);
        } else {
          RAST._IType _1476_tpe;
          RAST._IType _out105;
          _out105 = (this).GenType(_1471_instanceType, DCOMP.GenTypeContext.@default());
          _1476_tpe = _out105;
          if ((_1470_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1476_tpe = RAST.Type.create_Borrowed(_1476_tpe);
          } else if ((_1470_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1476_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1476_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1476_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _1476_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.Type.create_SelfOwned()));
              } else {
                _1476_tpe = RAST.Type.create_Borrowed(RAST.Type.create_SelfOwned());
              }
            }
          }
          _1461_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1470_selfId, _1476_tpe)), _1461_params);
        }
        _1469_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1470_selfId, _1471_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1477_retTypeArgs;
      _1477_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1478_typeI;
      _1478_typeI = BigInteger.Zero;
      while ((_1478_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1479_typeExpr;
        RAST._IType _out106;
        _out106 = (this).GenType(((m).dtor_outTypes).Select(_1478_typeI), DCOMP.GenTypeContext.@default());
        _1479_typeExpr = _out106;
        _1477_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1477_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1479_typeExpr));
        _1478_typeI = (_1478_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1480_visibility;
      _1480_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1481_typeParamsFiltered;
      _1481_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi29 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1482_typeParamI = BigInteger.Zero; _1482_typeParamI < _hi29; _1482_typeParamI++) {
        DAST._ITypeArgDecl _1483_typeParam;
        _1483_typeParam = ((m).dtor_typeParams).Select(_1482_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1483_typeParam).dtor_name)))) {
          _1481_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1481_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1483_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1484_typeParams;
      _1484_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1481_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi30 = new BigInteger((_1481_typeParamsFiltered).Count);
        for (BigInteger _1485_i = BigInteger.Zero; _1485_i < _hi30; _1485_i++) {
          DAST._IType _1486_typeArg;
          RAST._ITypeParamDecl _1487_rTypeParamDecl;
          DAST._IType _out107;
          RAST._ITypeParamDecl _out108;
          (this).GenTypeParam((_1481_typeParamsFiltered).Select(_1485_i), out _out107, out _out108);
          _1486_typeArg = _out107;
          _1487_rTypeParamDecl = _out108;
          var _pat_let_tv144 = _1487_rTypeParamDecl;
          _1487_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1487_rTypeParamDecl, _pat_let34_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let34_0, _1488_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv144).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let35_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let35_0, _1489_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1488_dt__update__tmp_h1).dtor_content, _1489_dt__update_hconstraints_h0)))));
          _1484_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1484_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1487_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1490_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1491_env = DCOMP.Environment.Default();
      RAST._IExpr _1492_preBody;
      _1492_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1493_preAssignNames;
      _1493_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1494_preAssignTypes;
      _1494_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1495_earlyReturn;
        _1495_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source70 = (m).dtor_outVars;
        bool unmatched70 = true;
        if (unmatched70) {
          if (_source70.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1496_outVars = _source70.dtor_value;
            unmatched70 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1495_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi31 = new BigInteger((_1496_outVars).Count);
                for (BigInteger _1497_outI = BigInteger.Zero; _1497_outI < _hi31; _1497_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1498_outVar;
                  _1498_outVar = (_1496_outVars).Select(_1497_outI);
                  Dafny.ISequence<Dafny.Rune> _1499_outName;
                  _1499_outName = DCOMP.__default.escapeVar((_1498_outVar));
                  Dafny.ISequence<Dafny.Rune> _1500_tracker__name;
                  _1500_tracker__name = DCOMP.__default.AddAssignedPrefix(_1499_outName);
                  _1493_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1493_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1500_tracker__name));
                  _1494_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1494_preAssignTypes, _1500_tracker__name, RAST.Type.create_Bool());
                  _1492_preBody = (_1492_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1500_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1501_tupleArgs;
                _1501_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi32 = new BigInteger((_1496_outVars).Count);
                for (BigInteger _1502_outI = BigInteger.Zero; _1502_outI < _hi32; _1502_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1503_outVar;
                  _1503_outVar = (_1496_outVars).Select(_1502_outI);
                  RAST._IType _1504_outType;
                  RAST._IType _out109;
                  _out109 = (this).GenType(((m).dtor_outTypes).Select(_1502_outI), DCOMP.GenTypeContext.@default());
                  _1504_outType = _out109;
                  Dafny.ISequence<Dafny.Rune> _1505_outName;
                  _1505_outName = DCOMP.__default.escapeVar((_1503_outVar));
                  _1462_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1462_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1505_outName));
                  RAST._IType _1506_outMaybeType;
                  _1506_outMaybeType = (((_1504_outType).CanReadWithoutClone()) ? (_1504_outType) : (RAST.__default.MaybePlaceboType(_1504_outType)));
                  _1463_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1463_paramTypes, _1505_outName, _1506_outMaybeType);
                  _1501_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1501_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1505_outName));
                }
                _1495_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_1501_tupleArgs);
              }
            }
          }
        }
        if (unmatched70) {
          unmatched70 = false;
        }
        _1491_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1493_preAssignNames, _1462_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1494_preAssignTypes, _1463_paramTypes));
        RAST._IExpr _1507_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1508___v69;
        DCOMP._IEnvironment _1509___v70;
        RAST._IExpr _out110;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
        DCOMP._IEnvironment _out112;
        (this).GenStmts((m).dtor_body, _1469_selfIdent, _1491_env, true, _1495_earlyReturn, out _out110, out _out111, out _out112);
        _1507_body = _out110;
        _1508___v69 = _out111;
        _1509___v70 = _out112;
        _1490_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1492_preBody).Then(_1507_body));
      } else {
        _1491_env = DCOMP.Environment.create(_1462_paramNames, _1463_paramTypes);
        _1490_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1480_visibility, RAST.Fn.create(_1468_fnName, _1484_typeParams, _1461_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1477_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1477_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1477_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1490_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1510_declarations;
      _1510_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1511_i;
      _1511_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1512_stmts;
      _1512_stmts = stmts;
      while ((_1511_i) < (new BigInteger((_1512_stmts).Count))) {
        DAST._IStatement _1513_stmt;
        _1513_stmt = (_1512_stmts).Select(_1511_i);
        DAST._IStatement _source71 = _1513_stmt;
        bool unmatched71 = true;
        if (unmatched71) {
          if (_source71.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1514_name = _source71.dtor_name;
            DAST._IType _1515_optType = _source71.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source71.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched71 = false;
              if (((_1511_i) + (BigInteger.One)) < (new BigInteger((_1512_stmts).Count))) {
                DAST._IStatement _source72 = (_1512_stmts).Select((_1511_i) + (BigInteger.One));
                bool unmatched72 = true;
                if (unmatched72) {
                  if (_source72.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source72.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _1516_name2 = ident0;
                      DAST._IExpression _1517_rhs = _source72.dtor_value;
                      unmatched72 = false;
                      if (object.Equals(_1516_name2, _1514_name)) {
                        _1512_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1512_stmts).Subsequence(BigInteger.Zero, _1511_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1514_name, _1515_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1517_rhs)))), (_1512_stmts).Drop((_1511_i) + (new BigInteger(2))));
                        _1513_stmt = (_1512_stmts).Select(_1511_i);
                      }
                    }
                  }
                }
                if (unmatched72) {
                  unmatched72 = false;
                }
              }
            }
          }
        }
        if (unmatched71) {
          unmatched71 = false;
        }
        RAST._IExpr _1518_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1519_recIdents;
        DCOMP._IEnvironment _1520_newEnv2;
        RAST._IExpr _out113;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out114;
        DCOMP._IEnvironment _out115;
        (this).GenStmt(_1513_stmt, selfIdent, newEnv, (isLast) && ((_1511_i) == ((new BigInteger((_1512_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out113, out _out114, out _out115);
        _1518_stmtExpr = _out113;
        _1519_recIdents = _out114;
        _1520_newEnv2 = _out115;
        newEnv = _1520_newEnv2;
        DAST._IStatement _source73 = _1513_stmt;
        bool unmatched73 = true;
        if (unmatched73) {
          if (_source73.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1521_name = _source73.dtor_name;
            unmatched73 = false;
            {
              _1510_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1510_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_1521_name)));
            }
          }
        }
        if (unmatched73) {
          unmatched73 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1519_recIdents, _1510_declarations));
        generated = (generated).Then(_1518_stmtExpr);
        _1511_i = (_1511_i) + (BigInteger.One);
        if ((_1518_stmtExpr).is_Return) {
          goto after_0;
        }
      continue_0: ;
      }
    after_0: ;
    }
    public void GenAssignLhs(DAST._IAssignLhs lhs, RAST._IExpr rhs, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, out RAST._IExpr generated, out bool needsIIFE, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      needsIIFE = false;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      newEnv = env;
      DAST._IAssignLhs _source74 = lhs;
      bool unmatched74 = true;
      if (unmatched74) {
        if (_source74.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident1 = _source74.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _1522_id = ident1;
          unmatched74 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1523_idRust;
            _1523_idRust = DCOMP.__default.escapeVar(_1522_id);
            if (((env).IsBorrowed(_1523_idRust)) || ((env).IsBorrowedMut(_1523_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1523_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1523_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1523_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Select) {
          DAST._IExpression _1524_on = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1525_field = _source74.dtor_field;
          unmatched74 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1526_fieldName;
            _1526_fieldName = DCOMP.__default.escapeName(_1525_field);
            RAST._IExpr _1527_onExpr;
            DCOMP._IOwnership _1528_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1529_recIdents;
            RAST._IExpr _out116;
            DCOMP._IOwnership _out117;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out118;
            (this).GenExpr(_1524_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out116, out _out117, out _out118);
            _1527_onExpr = _out116;
            _1528_onOwned = _out117;
            _1529_recIdents = _out118;
            RAST._IExpr _source75 = _1527_onExpr;
            bool unmatched75 = true;
            if (unmatched75) {
              bool disjunctiveMatch11 = false;
              if (_source75.is_Call) {
                RAST._IExpr obj2 = _source75.dtor_obj;
                if (obj2.is_Select) {
                  RAST._IExpr obj3 = obj2.dtor_obj;
                  if (obj3.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name9 = obj3.dtor_name;
                    if (object.Equals(name9, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      Dafny.ISequence<Dafny.Rune> name10 = obj2.dtor_name;
                      if (object.Equals(name10, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                        disjunctiveMatch11 = true;
                      }
                    }
                  }
                }
              }
              if (_source75.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name11 = _source75.dtor_name;
                if (object.Equals(name11, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch11 = true;
                }
              }
              if (_source75.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op14 = _source75.dtor_op1;
                if (object.Equals(op14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying4 = _source75.dtor_underlying;
                  if (underlying4.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name12 = underlying4.dtor_name;
                    if (object.Equals(name12, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      disjunctiveMatch11 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch11) {
                unmatched75 = false;
                Dafny.ISequence<Dafny.Rune> _1530_isAssignedVar;
                _1530_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1526_fieldName);
                if (((newEnv).dtor_names).Contains(_1530_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1526_fieldName), RAST.Expr.create_Identifier(_1530_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1530_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1530_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1526_fieldName, rhs);
                }
              }
            }
            if (unmatched75) {
              unmatched75 = false;
              if (!object.Equals(_1527_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1527_onExpr = ((this).modify__macro).Apply1(_1527_onExpr);
              }
              generated = RAST.__default.AssignMember(_1527_onExpr, _1526_fieldName, rhs);
            }
            readIdents = _1529_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched74) {
        DAST._IExpression _1531_on = _source74.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1532_indices = _source74.dtor_indices;
        unmatched74 = false;
        {
          RAST._IExpr _1533_onExpr;
          DCOMP._IOwnership _1534_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1535_recIdents;
          RAST._IExpr _out119;
          DCOMP._IOwnership _out120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
          (this).GenExpr(_1531_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out119, out _out120, out _out121);
          _1533_onExpr = _out119;
          _1534_onOwned = _out120;
          _1535_recIdents = _out121;
          readIdents = _1535_recIdents;
          _1533_onExpr = ((this).modify__macro).Apply1(_1533_onExpr);
          RAST._IExpr _1536_r;
          _1536_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1537_indicesExpr;
          _1537_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi33 = new BigInteger((_1532_indices).Count);
          for (BigInteger _1538_i = BigInteger.Zero; _1538_i < _hi33; _1538_i++) {
            RAST._IExpr _1539_idx;
            DCOMP._IOwnership _1540___v79;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1541_recIdentsIdx;
            RAST._IExpr _out122;
            DCOMP._IOwnership _out123;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
            (this).GenExpr((_1532_indices).Select(_1538_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out122, out _out123, out _out124);
            _1539_idx = _out122;
            _1540___v79 = _out123;
            _1541_recIdentsIdx = _out124;
            Dafny.ISequence<Dafny.Rune> _1542_varName;
            _1542_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1538_i));
            _1537_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1537_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1542_varName)));
            _1536_r = (_1536_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1542_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1539_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1541_recIdentsIdx);
          }
          if ((new BigInteger((_1532_indices).Count)) > (BigInteger.One)) {
            _1533_onExpr = (_1533_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1543_rhs;
          _1543_rhs = rhs;
          var _pat_let_tv145 = env;
          if (((_1533_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1533_onExpr).LhsIdentifierName(), _pat_let36_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let36_0, _1544_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv145).GetType(_1544_name), _pat_let37_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let37_0, _1545_tpe => ((_1545_tpe).is_Some) && (((_1545_tpe).dtor_value).IsUninitArray())))))))) {
            _1543_rhs = RAST.__default.MaybeUninitNew(_1543_rhs);
          }
          generated = (_1536_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1533_onExpr, _1537_indicesExpr)), _1543_rhs));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source76 = stmt;
      bool unmatched76 = true;
      if (unmatched76) {
        if (_source76.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1546_fields = _source76.dtor_fields;
          unmatched76 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi34 = new BigInteger((_1546_fields).Count);
            for (BigInteger _1547_i = BigInteger.Zero; _1547_i < _hi34; _1547_i++) {
              DAST._IFormal _1548_field;
              _1548_field = (_1546_fields).Select(_1547_i);
              Dafny.ISequence<Dafny.Rune> _1549_fieldName;
              _1549_fieldName = DCOMP.__default.escapeName((_1548_field).dtor_name);
              RAST._IType _1550_fieldTyp;
              RAST._IType _out125;
              _out125 = (this).GenType((_1548_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1550_fieldTyp = _out125;
              Dafny.ISequence<Dafny.Rune> _1551_isAssignedVar;
              _1551_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1549_fieldName);
              if (((newEnv).dtor_names).Contains(_1551_isAssignedVar)) {
                RAST._IExpr _1552_rhs;
                DCOMP._IOwnership _1553___v80;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1554___v81;
                RAST._IExpr _out126;
                DCOMP._IOwnership _out127;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1548_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out126, out _out127, out _out128);
                _1552_rhs = _out126;
                _1553___v80 = _out127;
                _1554___v81 = _out128;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1551_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1549_fieldName), RAST.Expr.create_Identifier(_1551_isAssignedVar), _1552_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1551_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1555_name = _source76.dtor_name;
          DAST._IType _1556_typ = _source76.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source76.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1557_expression = maybeValue1.dtor_value;
            unmatched76 = false;
            {
              RAST._IType _1558_tpe;
              RAST._IType _out129;
              _out129 = (this).GenType(_1556_typ, DCOMP.GenTypeContext.InBinding());
              _1558_tpe = _out129;
              Dafny.ISequence<Dafny.Rune> _1559_varName;
              _1559_varName = DCOMP.__default.escapeVar(_1555_name);
              bool _1560_hasCopySemantics;
              _1560_hasCopySemantics = (_1558_tpe).CanReadWithoutClone();
              if (((_1557_expression).is_InitializationValue) && (!(_1560_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1559_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1558_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1559_varName, RAST.__default.MaybePlaceboType(_1558_tpe));
              } else {
                RAST._IExpr _1561_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1562_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1557_expression).is_InitializationValue) && ((_1558_tpe).IsObjectOrPointer())) {
                  _1561_expr = (_1558_tpe).ToNullExpr();
                  _1562_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1563_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out130;
                  DCOMP._IOwnership _out131;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out132;
                  (this).GenExpr(_1557_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out130, out _out131, out _out132);
                  _1561_expr = _out130;
                  _1563_exprOwnership = _out131;
                  _1562_recIdents = _out132;
                }
                readIdents = _1562_recIdents;
                _1558_tpe = (((_1557_expression).is_NewUninitArray) ? ((_1558_tpe).TypeAtInitialization()) : (_1558_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1559_varName, Std.Wrappers.Option<RAST._IType>.create_Some(_1558_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1561_expr));
                newEnv = (env).AddAssigned(_1559_varName, _1558_tpe);
              }
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1564_name = _source76.dtor_name;
          DAST._IType _1565_typ = _source76.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source76.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched76 = false;
            {
              DAST._IStatement _1566_newStmt;
              _1566_newStmt = DAST.Statement.create_DeclareVar(_1564_name, _1565_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1565_typ)));
              RAST._IExpr _out133;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out134;
              DCOMP._IEnvironment _out135;
              (this).GenStmt(_1566_newStmt, selfIdent, env, isLast, earlyReturn, out _out133, out _out134, out _out135);
              generated = _out133;
              readIdents = _out134;
              newEnv = _out135;
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Assign) {
          DAST._IAssignLhs _1567_lhs = _source76.dtor_lhs;
          DAST._IExpression _1568_expression = _source76.dtor_value;
          unmatched76 = false;
          {
            RAST._IExpr _1569_exprGen;
            DCOMP._IOwnership _1570___v82;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1571_exprIdents;
            RAST._IExpr _out136;
            DCOMP._IOwnership _out137;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out138;
            (this).GenExpr(_1568_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out136, out _out137, out _out138);
            _1569_exprGen = _out136;
            _1570___v82 = _out137;
            _1571_exprIdents = _out138;
            if ((_1567_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1572_rustId;
              _1572_rustId = DCOMP.__default.escapeVar(((_1567_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1573_tpe;
              _1573_tpe = (env).GetType(_1572_rustId);
              if (((_1573_tpe).is_Some) && ((((_1573_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1569_exprGen = RAST.__default.MaybePlacebo(_1569_exprGen);
              }
            }
            if (((_1567_lhs).is_Index) && (((_1567_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1574_rustId;
              _1574_rustId = DCOMP.__default.escapeVar(((_1567_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1575_tpe;
              _1575_tpe = (env).GetType(_1574_rustId);
              if (((_1575_tpe).is_Some) && ((((_1575_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1569_exprGen = RAST.__default.MaybeUninitNew(_1569_exprGen);
              }
            }
            RAST._IExpr _1576_lhsGen;
            bool _1577_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1578_recIdents;
            DCOMP._IEnvironment _1579_resEnv;
            RAST._IExpr _out139;
            bool _out140;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
            DCOMP._IEnvironment _out142;
            (this).GenAssignLhs(_1567_lhs, _1569_exprGen, selfIdent, env, out _out139, out _out140, out _out141, out _out142);
            _1576_lhsGen = _out139;
            _1577_needsIIFE = _out140;
            _1578_recIdents = _out141;
            _1579_resEnv = _out142;
            generated = _1576_lhsGen;
            newEnv = _1579_resEnv;
            if (_1577_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1578_recIdents, _1571_exprIdents);
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_If) {
          DAST._IExpression _1580_cond = _source76.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1581_thnDafny = _source76.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1582_elsDafny = _source76.dtor_els;
          unmatched76 = false;
          {
            RAST._IExpr _1583_cond;
            DCOMP._IOwnership _1584___v83;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1585_recIdents;
            RAST._IExpr _out143;
            DCOMP._IOwnership _out144;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out145;
            (this).GenExpr(_1580_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out143, out _out144, out _out145);
            _1583_cond = _out143;
            _1584___v83 = _out144;
            _1585_recIdents = _out145;
            Dafny.ISequence<Dafny.Rune> _1586_condString;
            _1586_condString = (_1583_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1585_recIdents;
            RAST._IExpr _1587_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1588_thnIdents;
            DCOMP._IEnvironment _1589_thnEnv;
            RAST._IExpr _out146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
            DCOMP._IEnvironment _out148;
            (this).GenStmts(_1581_thnDafny, selfIdent, env, isLast, earlyReturn, out _out146, out _out147, out _out148);
            _1587_thn = _out146;
            _1588_thnIdents = _out147;
            _1589_thnEnv = _out148;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1588_thnIdents);
            RAST._IExpr _1590_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1591_elsIdents;
            DCOMP._IEnvironment _1592_elsEnv;
            RAST._IExpr _out149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out150;
            DCOMP._IEnvironment _out151;
            (this).GenStmts(_1582_elsDafny, selfIdent, env, isLast, earlyReturn, out _out149, out _out150, out _out151);
            _1590_els = _out149;
            _1591_elsIdents = _out150;
            _1592_elsEnv = _out151;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1591_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1583_cond, _1587_thn, _1590_els);
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1593_lbl = _source76.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1594_body = _source76.dtor_body;
          unmatched76 = false;
          {
            RAST._IExpr _1595_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1596_bodyIdents;
            DCOMP._IEnvironment _1597_env2;
            RAST._IExpr _out152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
            DCOMP._IEnvironment _out154;
            (this).GenStmts(_1594_body, selfIdent, env, isLast, earlyReturn, out _out152, out _out153, out _out154);
            _1595_body = _out152;
            _1596_bodyIdents = _out153;
            _1597_env2 = _out154;
            readIdents = _1596_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1593_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1595_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_While) {
          DAST._IExpression _1598_cond = _source76.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1599_body = _source76.dtor_body;
          unmatched76 = false;
          {
            RAST._IExpr _1600_cond;
            DCOMP._IOwnership _1601___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1602_recIdents;
            RAST._IExpr _out155;
            DCOMP._IOwnership _out156;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out157;
            (this).GenExpr(_1598_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out155, out _out156, out _out157);
            _1600_cond = _out155;
            _1601___v84 = _out156;
            _1602_recIdents = _out157;
            readIdents = _1602_recIdents;
            RAST._IExpr _1603_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1604_bodyIdents;
            DCOMP._IEnvironment _1605_bodyEnv;
            RAST._IExpr _out158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
            DCOMP._IEnvironment _out160;
            (this).GenStmts(_1599_body, selfIdent, env, false, earlyReturn, out _out158, out _out159, out _out160);
            _1603_bodyExpr = _out158;
            _1604_bodyIdents = _out159;
            _1605_bodyEnv = _out160;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1604_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1600_cond), _1603_bodyExpr);
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1606_boundName = _source76.dtor_boundName;
          DAST._IType _1607_boundType = _source76.dtor_boundType;
          DAST._IExpression _1608_overExpr = _source76.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1609_body = _source76.dtor_body;
          unmatched76 = false;
          {
            RAST._IExpr _1610_over;
            DCOMP._IOwnership _1611___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1612_recIdents;
            RAST._IExpr _out161;
            DCOMP._IOwnership _out162;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out163;
            (this).GenExpr(_1608_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out161, out _out162, out _out163);
            _1610_over = _out161;
            _1611___v85 = _out162;
            _1612_recIdents = _out163;
            if (((_1608_overExpr).is_MapBoundedPool) || ((_1608_overExpr).is_SetBoundedPool)) {
              _1610_over = ((_1610_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1613_boundTpe;
            RAST._IType _out164;
            _out164 = (this).GenType(_1607_boundType, DCOMP.GenTypeContext.@default());
            _1613_boundTpe = _out164;
            readIdents = _1612_recIdents;
            Dafny.ISequence<Dafny.Rune> _1614_boundRName;
            _1614_boundRName = DCOMP.__default.escapeVar(_1606_boundName);
            RAST._IExpr _1615_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1616_bodyIdents;
            DCOMP._IEnvironment _1617_bodyEnv;
            RAST._IExpr _out165;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out166;
            DCOMP._IEnvironment _out167;
            (this).GenStmts(_1609_body, selfIdent, (env).AddAssigned(_1614_boundRName, _1613_boundTpe), false, earlyReturn, out _out165, out _out166, out _out167);
            _1615_bodyExpr = _out165;
            _1616_bodyIdents = _out166;
            _1617_bodyEnv = _out167;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1616_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1614_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1614_boundRName, _1610_over, _1615_bodyExpr);
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1618_toLabel = _source76.dtor_toLabel;
          unmatched76 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source77 = _1618_toLabel;
            bool unmatched77 = true;
            if (unmatched77) {
              if (_source77.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1619_lbl = _source77.dtor_value;
                unmatched77 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1619_lbl)));
                }
              }
            }
            if (unmatched77) {
              unmatched77 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1620_body = _source76.dtor_body;
          unmatched76 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1621_selfClone;
              DCOMP._IOwnership _1622___v86;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1623___v87;
              RAST._IExpr _out168;
              DCOMP._IOwnership _out169;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out170;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out168, out _out169, out _out170);
              _1621_selfClone = _out168;
              _1622___v86 = _out169;
              _1623___v87 = _out170;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1621_selfClone)));
            }
            newEnv = env;
            BigInteger _hi35 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1624_paramI = BigInteger.Zero; _1624_paramI < _hi35; _1624_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1625_param;
              _1625_param = ((env).dtor_names).Select(_1624_paramI);
              RAST._IExpr _1626_paramInit;
              DCOMP._IOwnership _1627___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1628___v89;
              RAST._IExpr _out171;
              DCOMP._IOwnership _out172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
              (this).GenIdent(_1625_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out171, out _out172, out _out173);
              _1626_paramInit = _out171;
              _1627___v88 = _out172;
              _1628___v89 = _out173;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1625_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1626_paramInit)));
              if (((env).dtor_types).Contains(_1625_param)) {
                RAST._IType _1629_declaredType;
                _1629_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1625_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1625_param, _1629_declaredType);
              }
            }
            RAST._IExpr _1630_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1631_bodyIdents;
            DCOMP._IEnvironment _1632_bodyEnv;
            RAST._IExpr _out174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out175;
            DCOMP._IEnvironment _out176;
            (this).GenStmts(_1620_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out174, out _out175, out _out176);
            _1630_bodyExpr = _out174;
            _1631_bodyIdents = _out175;
            _1632_bodyEnv = _out176;
            readIdents = _1631_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1630_bodyExpr)));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_JumpTailCallStart) {
          unmatched76 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Call) {
          DAST._IExpression _1633_on = _source76.dtor_on;
          DAST._ICallName _1634_name = _source76.dtor_callName;
          Dafny.ISequence<DAST._IType> _1635_typeArgs = _source76.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1636_args = _source76.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1637_maybeOutVars = _source76.dtor_outs;
          unmatched76 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1638_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1639_recIdents;
            Dafny.ISequence<RAST._IType> _1640_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1641_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out178;
            Dafny.ISequence<RAST._IType> _out179;
            Std.Wrappers._IOption<DAST._IResolvedType> _out180;
            (this).GenArgs(selfIdent, _1634_name, _1635_typeArgs, _1636_args, env, out _out177, out _out178, out _out179, out _out180);
            _1638_argExprs = _out177;
            _1639_recIdents = _out178;
            _1640_typeExprs = _out179;
            _1641_fullNameQualifier = _out180;
            readIdents = _1639_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source78 = _1641_fullNameQualifier;
            bool unmatched78 = true;
            if (unmatched78) {
              if (_source78.is_Some) {
                DAST._IResolvedType value9 = _source78.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1642_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1643_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1644_base = value9.dtor_kind;
                unmatched78 = false;
                RAST._IExpr _1645_fullPath;
                RAST._IExpr _out181;
                _out181 = DCOMP.COMP.GenPathExpr(_1642_path, true);
                _1645_fullPath = _out181;
                Dafny.ISequence<RAST._IType> _1646_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out182;
                _out182 = (this).GenTypeArgs(_1643_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1646_onTypeExprs = _out182;
                RAST._IExpr _1647_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1648_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1649_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1644_base).is_Trait) || ((_1644_base).is_Class)) {
                  RAST._IExpr _out183;
                  DCOMP._IOwnership _out184;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out185;
                  (this).GenExpr(_1633_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out183, out _out184, out _out185);
                  _1647_onExpr = _out183;
                  _1648_recOwnership = _out184;
                  _1649_recIdents = _out185;
                  _1647_onExpr = ((this).modify__macro).Apply1(_1647_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1649_recIdents);
                } else {
                  RAST._IExpr _out186;
                  DCOMP._IOwnership _out187;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out188;
                  (this).GenExpr(_1633_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out186, out _out187, out _out188);
                  _1647_onExpr = _out186;
                  _1648_recOwnership = _out187;
                  _1649_recIdents = _out188;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1649_recIdents);
                }
                generated = ((((_1645_fullPath).ApplyType(_1646_onTypeExprs)).MSel(DCOMP.__default.escapeName((_1634_name).dtor_name))).ApplyType(_1640_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1647_onExpr), _1638_argExprs));
              }
            }
            if (unmatched78) {
              unmatched78 = false;
              RAST._IExpr _1650_onExpr;
              DCOMP._IOwnership _1651___v94;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1652_enclosingIdents;
              RAST._IExpr _out189;
              DCOMP._IOwnership _out190;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out191;
              (this).GenExpr(_1633_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out189, out _out190, out _out191);
              _1650_onExpr = _out189;
              _1651___v94 = _out190;
              _1652_enclosingIdents = _out191;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1652_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1653_renderedName;
              _1653_renderedName = (this).GetMethodName(_1633_on, _1634_name);
              DAST._IExpression _source79 = _1633_on;
              bool unmatched79 = true;
              if (unmatched79) {
                bool disjunctiveMatch12 = false;
                if (_source79.is_Companion) {
                  disjunctiveMatch12 = true;
                }
                if (_source79.is_ExternCompanion) {
                  disjunctiveMatch12 = true;
                }
                if (disjunctiveMatch12) {
                  unmatched79 = false;
                  {
                    _1650_onExpr = (_1650_onExpr).MSel(_1653_renderedName);
                  }
                }
              }
              if (unmatched79) {
                unmatched79 = false;
                {
                  if (!object.Equals(_1650_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source80 = _1634_name;
                    bool unmatched80 = true;
                    if (unmatched80) {
                      if (_source80.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source80.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1654_tpe = onType0.dtor_value;
                          unmatched80 = false;
                          RAST._IType _1655_typ;
                          RAST._IType _out192;
                          _out192 = (this).GenType(_1654_tpe, DCOMP.GenTypeContext.@default());
                          _1655_typ = _out192;
                          if (((_1655_typ).IsObjectOrPointer()) && (!object.Equals(_1650_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1650_onExpr = ((this).modify__macro).Apply1(_1650_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched80) {
                      unmatched80 = false;
                    }
                  }
                  _1650_onExpr = (_1650_onExpr).Sel(_1653_renderedName);
                }
              }
              generated = ((_1650_onExpr).ApplyType(_1640_typeExprs)).Apply(_1638_argExprs);
            }
            if (((_1637_maybeOutVars).is_Some) && ((new BigInteger(((_1637_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1656_outVar;
              _1656_outVar = DCOMP.__default.escapeVar((((_1637_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1656_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1656_outVar, generated);
            } else if (((_1637_maybeOutVars).is_None) || ((new BigInteger(((_1637_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1657_tmpVar;
              _1657_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1658_tmpId;
              _1658_tmpId = RAST.Expr.create_Identifier(_1657_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1657_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1659_outVars;
              _1659_outVars = (_1637_maybeOutVars).dtor_value;
              BigInteger _hi36 = new BigInteger((_1659_outVars).Count);
              for (BigInteger _1660_outI = BigInteger.Zero; _1660_outI < _hi36; _1660_outI++) {
                Dafny.ISequence<Dafny.Rune> _1661_outVar;
                _1661_outVar = DCOMP.__default.escapeVar(((_1659_outVars).Select(_1660_outI)));
                RAST._IExpr _1662_rhs;
                _1662_rhs = (_1658_tmpId).Sel(Std.Strings.__default.OfNat(_1660_outI));
                if (!((env).CanReadWithoutClone(_1661_outVar))) {
                  _1662_rhs = RAST.__default.MaybePlacebo(_1662_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1661_outVar, _1662_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Return) {
          DAST._IExpression _1663_exprDafny = _source76.dtor_expr;
          unmatched76 = false;
          {
            RAST._IExpr _1664_expr;
            DCOMP._IOwnership _1665___v104;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1666_recIdents;
            RAST._IExpr _out193;
            DCOMP._IOwnership _out194;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out195;
            (this).GenExpr(_1663_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out193, out _out194, out _out195);
            _1664_expr = _out193;
            _1665___v104 = _out194;
            _1666_recIdents = _out195;
            readIdents = _1666_recIdents;
            if (isLast) {
              generated = _1664_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1664_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_EarlyReturn) {
          unmatched76 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source81 = earlyReturn;
            bool unmatched81 = true;
            if (unmatched81) {
              if (_source81.is_None) {
                unmatched81 = false;
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
              }
            }
            if (unmatched81) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1667_rustIdents = _source81.dtor_value;
              unmatched81 = false;
              Dafny.ISequence<RAST._IExpr> _1668_tupleArgs;
              _1668_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi37 = new BigInteger((_1667_rustIdents).Count);
              for (BigInteger _1669_i = BigInteger.Zero; _1669_i < _hi37; _1669_i++) {
                RAST._IExpr _1670_rIdent;
                DCOMP._IOwnership _1671___v105;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1672___v106;
                RAST._IExpr _out196;
                DCOMP._IOwnership _out197;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out198;
                (this).GenIdent((_1667_rustIdents).Select(_1669_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out196, out _out197, out _out198);
                _1670_rIdent = _out196;
                _1671___v105 = _out197;
                _1672___v106 = _out198;
                _1668_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1668_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1670_rIdent));
              }
              if ((new BigInteger((_1668_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1668_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1668_tupleArgs)));
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Halt) {
          unmatched76 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched76) {
        DAST._IExpression _1673_e = _source76.dtor_Print_a0;
        unmatched76 = false;
        {
          RAST._IExpr _1674_printedExpr;
          DCOMP._IOwnership _1675_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1676_recIdents;
          RAST._IExpr _out199;
          DCOMP._IOwnership _out200;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
          (this).GenExpr(_1673_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out199, out _out200, out _out201);
          _1674_printedExpr = _out199;
          _1675_recOwnership = _out200;
          _1676_recIdents = _out201;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1674_printedExpr)));
          readIdents = _1676_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeRangeToRustType(DAST._INewtypeRange range) {
      DAST._INewtypeRange _source82 = range;
      bool unmatched82 = true;
      if (unmatched82) {
        if (_source82.is_NoRange) {
          unmatched82 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched82) {
        if (_source82.is_U8) {
          unmatched82 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched82) {
        if (_source82.is_U16) {
          unmatched82 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched82) {
        if (_source82.is_U32) {
          unmatched82 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched82) {
        if (_source82.is_U64) {
          unmatched82 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched82) {
        if (_source82.is_U128) {
          unmatched82 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched82) {
        if (_source82.is_I8) {
          unmatched82 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched82) {
        if (_source82.is_I16) {
          unmatched82 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched82) {
        if (_source82.is_I32) {
          unmatched82 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched82) {
        if (_source82.is_I64) {
          unmatched82 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched82) {
        if (_source82.is_I128) {
          unmatched82 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched82) {
        unmatched82 = false;
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
      throw new System.Exception("unexpected control point");
    }
    public void FromOwned(RAST._IExpr r, DCOMP._IOwnership expectedOwnership, out RAST._IExpr @out, out DCOMP._IOwnership resultingOwnership)
    {
      @out = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        @out = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
        @out = r;
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
        @out = RAST.__default.Borrow(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        @out = ((this).modify__macro).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((r)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/*TODO: Conversion from Borrowed or BorrowedMut to BorrowedMut*/"))));
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      }
    }
    public void FromOwnership(RAST._IExpr r, DCOMP._IOwnership ownership, DCOMP._IOwnership expectedOwnership, out RAST._IExpr @out, out DCOMP._IOwnership resultingOwnership)
    {
      @out = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      if (object.Equals(ownership, expectedOwnership)) {
        @out = r;
        resultingOwnership = expectedOwnership;
        return ;
      }
      if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwned())) {
        RAST._IExpr _out202;
        DCOMP._IOwnership _out203;
        (this).FromOwned(r, expectedOwnership, out _out202, out _out203);
        @out = _out202;
        resultingOwnership = _out203;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out204;
        DCOMP._IOwnership _out205;
        (this).FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out204, out _out205);
        @out = _out204;
        resultingOwnership = _out205;
      } else if ((object.Equals(ownership, DCOMP.Ownership.create_OwnershipBorrowed())) || (object.Equals(ownership, DCOMP.Ownership.create_OwnershipBorrowedMut()))) {
        if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
          @out = (r).Clone();
        } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
          @out = RAST.__default.BoxNew((r).Clone());
        } else if ((object.Equals(expectedOwnership, ownership)) || (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()))) {
          resultingOwnership = ownership;
          @out = r;
        } else if ((object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) && (object.Equals(ownership, DCOMP.Ownership.create_OwnershipBorrowedMut()))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
          @out = r;
        } else {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
          @out = RAST.__default.BorrowMut(r);
        }
      } else {
      }
    }
    public static bool OwnershipGuarantee(DCOMP._IOwnership expectedOwnership, DCOMP._IOwnership resultingOwnership)
    {
      return (!(!object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) || (object.Equals(resultingOwnership, expectedOwnership))) && (!object.Equals(resultingOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed()));
    }
    public void GenExprLiteral(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source83 = e;
      bool unmatched83 = true;
      if (unmatched83) {
        if (_source83.is_Literal) {
          DAST._ILiteral _h170 = _source83.dtor_Literal_a0;
          if (_h170.is_BoolLiteral) {
            bool _1677_b = _h170.dtor_BoolLiteral_a0;
            unmatched83 = false;
            {
              RAST._IExpr _out206;
              DCOMP._IOwnership _out207;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1677_b), expectedOwnership, out _out206, out _out207);
              r = _out206;
              resultingOwnership = _out207;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Literal) {
          DAST._ILiteral _h171 = _source83.dtor_Literal_a0;
          if (_h171.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1678_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1679_t = _h171.dtor_IntLiteral_a1;
            unmatched83 = false;
            {
              DAST._IType _source84 = _1679_t;
              bool unmatched84 = true;
              if (unmatched84) {
                if (_source84.is_Primitive) {
                  DAST._IPrimitive _h70 = _source84.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched84 = false;
                    {
                      if ((new BigInteger((_1678_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1678_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1678_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched84) {
                DAST._IType _1680_o = _source84;
                unmatched84 = false;
                {
                  RAST._IType _1681_genType;
                  RAST._IType _out208;
                  _out208 = (this).GenType(_1680_o, DCOMP.GenTypeContext.@default());
                  _1681_genType = _out208;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1678_i), _1681_genType);
                }
              }
              RAST._IExpr _out209;
              DCOMP._IOwnership _out210;
              (this).FromOwned(r, expectedOwnership, out _out209, out _out210);
              r = _out209;
              resultingOwnership = _out210;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Literal) {
          DAST._ILiteral _h172 = _source83.dtor_Literal_a0;
          if (_h172.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1682_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1683_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1684_t = _h172.dtor_DecLiteral_a2;
            unmatched83 = false;
            {
              DAST._IType _source85 = _1684_t;
              bool unmatched85 = true;
              if (unmatched85) {
                if (_source85.is_Primitive) {
                  DAST._IPrimitive _h71 = _source85.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched85 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1682_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1683_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched85) {
                DAST._IType _1685_o = _source85;
                unmatched85 = false;
                {
                  RAST._IType _1686_genType;
                  RAST._IType _out211;
                  _out211 = (this).GenType(_1685_o, DCOMP.GenTypeContext.@default());
                  _1686_genType = _out211;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1682_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1683_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1686_genType);
                }
              }
              RAST._IExpr _out212;
              DCOMP._IOwnership _out213;
              (this).FromOwned(r, expectedOwnership, out _out212, out _out213);
              r = _out212;
              resultingOwnership = _out213;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Literal) {
          DAST._ILiteral _h173 = _source83.dtor_Literal_a0;
          if (_h173.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1687_l = _h173.dtor_StringLiteral_a0;
            bool _1688_verbatim = _h173.dtor_verbatim;
            unmatched83 = false;
            {
              if (_1688_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1687_l, false, _1688_verbatim));
              RAST._IExpr _out214;
              DCOMP._IOwnership _out215;
              (this).FromOwned(r, expectedOwnership, out _out214, out _out215);
              r = _out214;
              resultingOwnership = _out215;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Literal) {
          DAST._ILiteral _h174 = _source83.dtor_Literal_a0;
          if (_h174.is_CharLiteralUTF16) {
            BigInteger _1689_c = _h174.dtor_CharLiteralUTF16_a0;
            unmatched83 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1689_c));
              r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out216;
              DCOMP._IOwnership _out217;
              (this).FromOwned(r, expectedOwnership, out _out216, out _out217);
              r = _out216;
              resultingOwnership = _out217;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Literal) {
          DAST._ILiteral _h175 = _source83.dtor_Literal_a0;
          if (_h175.is_CharLiteral) {
            Dafny.Rune _1690_c = _h175.dtor_CharLiteral_a0;
            unmatched83 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1690_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out218;
              DCOMP._IOwnership _out219;
              (this).FromOwned(r, expectedOwnership, out _out218, out _out219);
              r = _out218;
              resultingOwnership = _out219;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched83) {
        DAST._ILiteral _h176 = _source83.dtor_Literal_a0;
        DAST._IType _1691_tpe = _h176.dtor_Null_a0;
        unmatched83 = false;
        {
          RAST._IType _1692_tpeGen;
          RAST._IType _out220;
          _out220 = (this).GenType(_1691_tpe, DCOMP.GenTypeContext.@default());
          _1692_tpeGen = _out220;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"));
          } else {
            r = RAST.Expr.create_TypeAscription(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1692_tpeGen);
          }
          RAST._IExpr _out221;
          DCOMP._IOwnership _out222;
          (this).FromOwned(r, expectedOwnership, out _out221, out _out222);
          r = _out221;
          resultingOwnership = _out222;
          readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          return ;
        }
      }
    }
    public void GenExprBinary(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IBinOp _1693_op = _let_tmp_rhs54.dtor_op;
      DAST._IExpression _1694_lExpr = _let_tmp_rhs54.dtor_left;
      DAST._IExpression _1695_rExpr = _let_tmp_rhs54.dtor_right;
      DAST.Format._IBinaryOpFormat _1696_format = _let_tmp_rhs54.dtor_format2;
      bool _1697_becomesLeftCallsRight;
      _1697_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source86 = _1693_op;
        bool unmatched86 = true;
        if (unmatched86) {
          bool disjunctiveMatch13 = false;
          if (_source86.is_SetMerge) {
            disjunctiveMatch13 = true;
          }
          if (_source86.is_SetSubtraction) {
            disjunctiveMatch13 = true;
          }
          if (_source86.is_SetIntersection) {
            disjunctiveMatch13 = true;
          }
          if (_source86.is_SetDisjoint) {
            disjunctiveMatch13 = true;
          }
          if (_source86.is_MapMerge) {
            disjunctiveMatch13 = true;
          }
          if (_source86.is_MapSubtraction) {
            disjunctiveMatch13 = true;
          }
          if (_source86.is_MultisetMerge) {
            disjunctiveMatch13 = true;
          }
          if (_source86.is_MultisetSubtraction) {
            disjunctiveMatch13 = true;
          }
          if (_source86.is_MultisetIntersection) {
            disjunctiveMatch13 = true;
          }
          if (_source86.is_MultisetDisjoint) {
            disjunctiveMatch13 = true;
          }
          if (_source86.is_Concat) {
            disjunctiveMatch13 = true;
          }
          if (disjunctiveMatch13) {
            unmatched86 = false;
            return true;
          }
        }
        if (unmatched86) {
          unmatched86 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1698_becomesRightCallsLeft;
      _1698_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source87 = _1693_op;
        bool unmatched87 = true;
        if (unmatched87) {
          if (_source87.is_In) {
            unmatched87 = false;
            return true;
          }
        }
        if (unmatched87) {
          unmatched87 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1699_becomesCallLeftRight;
      _1699_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source88 = _1693_op;
        bool unmatched88 = true;
        if (unmatched88) {
          if (_source88.is_Eq) {
            bool referential0 = _source88.dtor_referential;
            if ((referential0) == (true)) {
              unmatched88 = false;
              return false;
            }
          }
        }
        if (unmatched88) {
          if (_source88.is_SetMerge) {
            unmatched88 = false;
            return true;
          }
        }
        if (unmatched88) {
          if (_source88.is_SetSubtraction) {
            unmatched88 = false;
            return true;
          }
        }
        if (unmatched88) {
          if (_source88.is_SetIntersection) {
            unmatched88 = false;
            return true;
          }
        }
        if (unmatched88) {
          if (_source88.is_SetDisjoint) {
            unmatched88 = false;
            return true;
          }
        }
        if (unmatched88) {
          if (_source88.is_MapMerge) {
            unmatched88 = false;
            return true;
          }
        }
        if (unmatched88) {
          if (_source88.is_MapSubtraction) {
            unmatched88 = false;
            return true;
          }
        }
        if (unmatched88) {
          if (_source88.is_MultisetMerge) {
            unmatched88 = false;
            return true;
          }
        }
        if (unmatched88) {
          if (_source88.is_MultisetSubtraction) {
            unmatched88 = false;
            return true;
          }
        }
        if (unmatched88) {
          if (_source88.is_MultisetIntersection) {
            unmatched88 = false;
            return true;
          }
        }
        if (unmatched88) {
          if (_source88.is_MultisetDisjoint) {
            unmatched88 = false;
            return true;
          }
        }
        if (unmatched88) {
          if (_source88.is_Concat) {
            unmatched88 = false;
            return true;
          }
        }
        if (unmatched88) {
          unmatched88 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1700_expectedLeftOwnership;
      _1700_expectedLeftOwnership = ((_1697_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1698_becomesRightCallsLeft) || (_1699_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1701_expectedRightOwnership;
      _1701_expectedRightOwnership = (((_1697_becomesLeftCallsRight) || (_1699_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1698_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1702_left;
      DCOMP._IOwnership _1703___v111;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1704_recIdentsL;
      RAST._IExpr _out223;
      DCOMP._IOwnership _out224;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out225;
      (this).GenExpr(_1694_lExpr, selfIdent, env, _1700_expectedLeftOwnership, out _out223, out _out224, out _out225);
      _1702_left = _out223;
      _1703___v111 = _out224;
      _1704_recIdentsL = _out225;
      RAST._IExpr _1705_right;
      DCOMP._IOwnership _1706___v112;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1707_recIdentsR;
      RAST._IExpr _out226;
      DCOMP._IOwnership _out227;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
      (this).GenExpr(_1695_rExpr, selfIdent, env, _1701_expectedRightOwnership, out _out226, out _out227, out _out228);
      _1705_right = _out226;
      _1706___v112 = _out227;
      _1707_recIdentsR = _out228;
      DAST._IBinOp _source89 = _1693_op;
      bool unmatched89 = true;
      if (unmatched89) {
        if (_source89.is_In) {
          unmatched89 = false;
          {
            r = ((_1705_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1702_left);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_SeqProperPrefix) {
          unmatched89 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1702_left, _1705_right, _1696_format);
        }
      }
      if (unmatched89) {
        if (_source89.is_SeqPrefix) {
          unmatched89 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1702_left, _1705_right, _1696_format);
        }
      }
      if (unmatched89) {
        if (_source89.is_SetMerge) {
          unmatched89 = false;
          {
            r = ((_1702_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1705_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_SetSubtraction) {
          unmatched89 = false;
          {
            r = ((_1702_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1705_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_SetIntersection) {
          unmatched89 = false;
          {
            r = ((_1702_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1705_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Subset) {
          unmatched89 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1702_left, _1705_right, _1696_format);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_ProperSubset) {
          unmatched89 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1702_left, _1705_right, _1696_format);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_SetDisjoint) {
          unmatched89 = false;
          {
            r = ((_1702_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1705_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_MapMerge) {
          unmatched89 = false;
          {
            r = ((_1702_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1705_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_MapSubtraction) {
          unmatched89 = false;
          {
            r = ((_1702_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1705_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_MultisetMerge) {
          unmatched89 = false;
          {
            r = ((_1702_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1705_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_MultisetSubtraction) {
          unmatched89 = false;
          {
            r = ((_1702_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1705_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_MultisetIntersection) {
          unmatched89 = false;
          {
            r = ((_1702_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1705_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Submultiset) {
          unmatched89 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1702_left, _1705_right, _1696_format);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_ProperSubmultiset) {
          unmatched89 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1702_left, _1705_right, _1696_format);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_MultisetDisjoint) {
          unmatched89 = false;
          {
            r = ((_1702_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1705_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Concat) {
          unmatched89 = false;
          {
            r = ((_1702_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1705_right);
          }
        }
      }
      if (unmatched89) {
        unmatched89 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1693_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1693_op), _1702_left, _1705_right, _1696_format);
          } else {
            DAST._IBinOp _source90 = _1693_op;
            bool unmatched90 = true;
            if (unmatched90) {
              if (_source90.is_Eq) {
                bool _1708_referential = _source90.dtor_referential;
                unmatched90 = false;
                {
                  if (_1708_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1702_left, _1705_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1695_rExpr).is_SeqValue) && ((new BigInteger(((_1695_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1702_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1694_lExpr).is_SeqValue) && ((new BigInteger(((_1694_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1705_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1702_left, _1705_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched90) {
              if (_source90.is_EuclidianDiv) {
                unmatched90 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1702_left, _1705_right));
                }
              }
            }
            if (unmatched90) {
              if (_source90.is_EuclidianMod) {
                unmatched90 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1702_left, _1705_right));
                }
              }
            }
            if (unmatched90) {
              Dafny.ISequence<Dafny.Rune> _1709_op = _source90.dtor_Passthrough_a0;
              unmatched90 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1709_op, _1702_left, _1705_right, _1696_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out229;
      DCOMP._IOwnership _out230;
      (this).FromOwned(r, expectedOwnership, out _out229, out _out230);
      r = _out229;
      resultingOwnership = _out230;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1704_recIdentsL, _1707_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1710_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1711_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1712_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1712_toTpe;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1713_path = _let_tmp_rhs57.dtor_path;
      Dafny.ISequence<DAST._IType> _1714_typeArgs = _let_tmp_rhs57.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs58 = _let_tmp_rhs57.dtor_kind;
      DAST._IType _1715_b = _let_tmp_rhs58.dtor_baseType;
      DAST._INewtypeRange _1716_range = _let_tmp_rhs58.dtor_range;
      bool _1717_erase = _let_tmp_rhs58.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1718___v114 = _let_tmp_rhs57.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1719___v115 = _let_tmp_rhs57.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1720___v116 = _let_tmp_rhs57.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1721_nativeToType;
      _1721_nativeToType = DCOMP.COMP.NewtypeRangeToRustType(_1716_range);
      if (object.Equals(_1711_fromTpe, _1715_b)) {
        RAST._IExpr _1722_recursiveGen;
        DCOMP._IOwnership _1723_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1724_recIdents;
        RAST._IExpr _out231;
        DCOMP._IOwnership _out232;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out233;
        (this).GenExpr(_1710_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out231, out _out232, out _out233);
        _1722_recursiveGen = _out231;
        _1723_recOwned = _out232;
        _1724_recIdents = _out233;
        readIdents = _1724_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source91 = _1721_nativeToType;
        bool unmatched91 = true;
        if (unmatched91) {
          if (_source91.is_Some) {
            RAST._IType _1725_v = _source91.dtor_value;
            unmatched91 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1722_recursiveGen, RAST.Expr.create_ExprFromType(_1725_v)));
            RAST._IExpr _out234;
            DCOMP._IOwnership _out235;
            (this).FromOwned(r, expectedOwnership, out _out234, out _out235);
            r = _out234;
            resultingOwnership = _out235;
          }
        }
        if (unmatched91) {
          unmatched91 = false;
          if (_1717_erase) {
            r = _1722_recursiveGen;
          } else {
            RAST._IType _1726_rhsType;
            RAST._IType _out236;
            _out236 = (this).GenType(_1712_toTpe, DCOMP.GenTypeContext.InBinding());
            _1726_rhsType = _out236;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1726_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1722_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out237;
          DCOMP._IOwnership _out238;
          (this).FromOwnership(r, _1723_recOwned, expectedOwnership, out _out237, out _out238);
          r = _out237;
          resultingOwnership = _out238;
        }
      } else {
        if ((_1721_nativeToType).is_Some) {
          DAST._IType _source92 = _1711_fromTpe;
          bool unmatched92 = true;
          if (unmatched92) {
            if (_source92.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source92.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1727_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1728_range0 = kind1.dtor_range;
                bool _1729_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1730_attributes0 = resolved1.dtor_attributes;
                unmatched92 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1731_nativeFromType;
                  _1731_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1728_range0);
                  if ((_1731_nativeFromType).is_Some) {
                    RAST._IExpr _1732_recursiveGen;
                    DCOMP._IOwnership _1733_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1734_recIdents;
                    RAST._IExpr _out239;
                    DCOMP._IOwnership _out240;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out241;
                    (this).GenExpr(_1710_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out239, out _out240, out _out241);
                    _1732_recursiveGen = _out239;
                    _1733_recOwned = _out240;
                    _1734_recIdents = _out241;
                    RAST._IExpr _out242;
                    DCOMP._IOwnership _out243;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1732_recursiveGen, (_1721_nativeToType).dtor_value), _1733_recOwned, expectedOwnership, out _out242, out _out243);
                    r = _out242;
                    resultingOwnership = _out243;
                    readIdents = _1734_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched92) {
            unmatched92 = false;
          }
          if (object.Equals(_1711_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1735_recursiveGen;
            DCOMP._IOwnership _1736_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1737_recIdents;
            RAST._IExpr _out244;
            DCOMP._IOwnership _out245;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out246;
            (this).GenExpr(_1710_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out244, out _out245, out _out246);
            _1735_recursiveGen = _out244;
            _1736_recOwned = _out245;
            _1737_recIdents = _out246;
            RAST._IExpr _out247;
            DCOMP._IOwnership _out248;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1735_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1721_nativeToType).dtor_value), _1736_recOwned, expectedOwnership, out _out247, out _out248);
            r = _out247;
            resultingOwnership = _out248;
            readIdents = _1737_recIdents;
            return ;
          }
        }
        RAST._IExpr _out249;
        DCOMP._IOwnership _out250;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out251;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1710_expr, _1711_fromTpe, _1715_b), _1715_b, _1712_toTpe), selfIdent, env, expectedOwnership, out _out249, out _out250, out _out251);
        r = _out249;
        resultingOwnership = _out250;
        readIdents = _out251;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs59 = e;
      DAST._IExpression _1738_expr = _let_tmp_rhs59.dtor_value;
      DAST._IType _1739_fromTpe = _let_tmp_rhs59.dtor_from;
      DAST._IType _1740_toTpe = _let_tmp_rhs59.dtor_typ;
      DAST._IType _let_tmp_rhs60 = _1739_fromTpe;
      DAST._IResolvedType _let_tmp_rhs61 = _let_tmp_rhs60.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1741___v122 = _let_tmp_rhs61.dtor_path;
      Dafny.ISequence<DAST._IType> _1742___v123 = _let_tmp_rhs61.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs62 = _let_tmp_rhs61.dtor_kind;
      DAST._IType _1743_b = _let_tmp_rhs62.dtor_baseType;
      DAST._INewtypeRange _1744_range = _let_tmp_rhs62.dtor_range;
      bool _1745_erase = _let_tmp_rhs62.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1746_attributes = _let_tmp_rhs61.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1747___v124 = _let_tmp_rhs61.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1748___v125 = _let_tmp_rhs61.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1749_nativeFromType;
      _1749_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1744_range);
      if (object.Equals(_1743_b, _1740_toTpe)) {
        RAST._IExpr _1750_recursiveGen;
        DCOMP._IOwnership _1751_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1752_recIdents;
        RAST._IExpr _out252;
        DCOMP._IOwnership _out253;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out254;
        (this).GenExpr(_1738_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out252, out _out253, out _out254);
        _1750_recursiveGen = _out252;
        _1751_recOwned = _out253;
        _1752_recIdents = _out254;
        readIdents = _1752_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source93 = _1749_nativeFromType;
        bool unmatched93 = true;
        if (unmatched93) {
          if (_source93.is_Some) {
            RAST._IType _1753_v = _source93.dtor_value;
            unmatched93 = false;
            RAST._IType _1754_toTpeRust;
            RAST._IType _out255;
            _out255 = (this).GenType(_1740_toTpe, DCOMP.GenTypeContext.@default());
            _1754_toTpeRust = _out255;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1754_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1750_recursiveGen));
            RAST._IExpr _out256;
            DCOMP._IOwnership _out257;
            (this).FromOwned(r, expectedOwnership, out _out256, out _out257);
            r = _out256;
            resultingOwnership = _out257;
          }
        }
        if (unmatched93) {
          unmatched93 = false;
          if (_1745_erase) {
            r = _1750_recursiveGen;
          } else {
            r = (_1750_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out258;
          DCOMP._IOwnership _out259;
          (this).FromOwnership(r, _1751_recOwned, expectedOwnership, out _out258, out _out259);
          r = _out258;
          resultingOwnership = _out259;
        }
      } else {
        if ((_1749_nativeFromType).is_Some) {
          if (object.Equals(_1740_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1755_recursiveGen;
            DCOMP._IOwnership _1756_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1757_recIdents;
            RAST._IExpr _out260;
            DCOMP._IOwnership _out261;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
            (this).GenExpr(_1738_expr, selfIdent, env, expectedOwnership, out _out260, out _out261, out _out262);
            _1755_recursiveGen = _out260;
            _1756_recOwned = _out261;
            _1757_recIdents = _out262;
            RAST._IExpr _out263;
            DCOMP._IOwnership _out264;
            (this).FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1755_recursiveGen, (this).DafnyCharUnderlying)), _1756_recOwned, expectedOwnership, out _out263, out _out264);
            r = _out263;
            resultingOwnership = _out264;
            readIdents = _1757_recIdents;
            return ;
          }
        }
        RAST._IExpr _out265;
        DCOMP._IOwnership _out266;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out267;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1738_expr, _1739_fromTpe, _1743_b), _1743_b, _1740_toTpe), selfIdent, env, expectedOwnership, out _out265, out _out266, out _out267);
        r = _out265;
        resultingOwnership = _out266;
        readIdents = _out267;
      }
    }
    public bool IsBuiltinCollection(DAST._IType typ) {
      return ((((typ).is_Seq) || ((typ).is_Set)) || ((typ).is_Map)) || ((typ).is_Multiset);
    }
    public DAST._IType GetBuiltinCollectionElement(DAST._IType typ) {
      if ((typ).is_Map) {
        return (typ).dtor_value;
      } else {
        return (typ).dtor_element;
      }
    }
    public bool SameTypesButDifferentTypeParameters(DAST._IType fromType, RAST._IType fromTpe, DAST._IType toType, RAST._IType toTpe)
    {
      return (((((((fromTpe).is_TypeApp) && ((toTpe).is_TypeApp)) && (object.Equals((fromTpe).dtor_baseName, (toTpe).dtor_baseName))) && ((fromType).is_UserDefined)) && ((toType).is_UserDefined)) && ((this).IsSameResolvedTypeAnyArgs((fromType).dtor_resolved, (toType).dtor_resolved))) && ((((new BigInteger((((fromType).dtor_resolved).dtor_typeArgs).Count)) == (new BigInteger((((toType).dtor_resolved).dtor_typeArgs).Count))) && ((new BigInteger((((toType).dtor_resolved).dtor_typeArgs).Count)) == (new BigInteger(((fromTpe).dtor_arguments).Count)))) && ((new BigInteger(((fromTpe).dtor_arguments).Count)) == (new BigInteger(((toTpe).dtor_arguments).Count))));
    }
    public Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> SeqResultToResultSeq<__T, __E>(Dafny.ISequence<Std.Wrappers._IResult<__T, __E>> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.FromElements());
      } else {
        Std.Wrappers._IResult<__T, __E> _1758_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1758_valueOrError0).IsFailure()) {
          return (_1758_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1759_head = (_1758_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1760_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1760_valueOrError1).IsFailure()) {
            return (_1760_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1761_tail = (_1760_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1759_head), _1761_tail));
          }
        }
      }
    }
    public Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> UpcastConversionLambda(DAST._IType fromType, RAST._IType fromTpe, DAST._IType toType, RAST._IType toTpe, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> typeParams)
    {
      if (object.Equals(fromTpe, toTpe)) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_id"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(fromTpe))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
      } else if (((fromTpe).IsObjectOrPointer()) && ((toTpe).IsObjectOrPointer())) {
        if (!(((toTpe).ObjectOrPointerUnderlying()).is_DynType)) {
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Failure(_System.Tuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>.create(fromType, fromTpe, toType, toTpe, typeParams));
        } else {
          RAST._IType _1762_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1763_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel((this).upcast)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1762_fromTpeUnderlying, _1763_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1764_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1764_valueOrError0).IsFailure()) {
          return (_1764_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1765_lambda = (_1764_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1765_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).Apply1(_1765_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1766_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim12 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr12 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
          for (int i12 = 0; i12 < dim12; i12++) {
            var _1767_i = (BigInteger) i12;
            arr12[(int)(_1767_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_1767_i), ((fromTpe).dtor_arguments).Select(_1767_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_1767_i), ((toTpe).dtor_arguments).Select(_1767_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr12);
        }))());
        if ((_1766_valueOrError1).IsFailure()) {
          return (_1766_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1768_lambdas = (_1766_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim13 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr13 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
  for (int i13 = 0; i13 < dim13; i13++) {
    var _1769_i = (BigInteger) i13;
    arr13[(int)(_1769_i)] = ((fromTpe).dtor_arguments).Select(_1769_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr13);
}))())).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1768_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1770_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1771_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1772_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1773_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1774_valueOrError2 = (this).UpcastConversionLambda(_1772_newFromType, _1770_newFromTpe, _1773_newToType, _1771_newToTpe, typeParams);
        if ((_1774_valueOrError2).IsFailure()) {
          return (_1774_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1775_coerceArg = (_1774_valueOrError2).Extract();
          RAST._IExpr _1776_collectionType = (RAST.__default.dafny__runtime).MSel((((fromTpe).Expand()).dtor_baseName).dtor_name);
          RAST._IExpr _1777_baseType = ((((((fromTpe).Expand()).dtor_baseName).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? ((_1776_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((((fromTpe).Expand()).dtor_arguments).Select(BigInteger.Zero), _1770_newFromTpe))) : ((_1776_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1770_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1777_baseType).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1775_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1778_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1778_valueOrError3).IsFailure()) {
          return (_1778_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1779_lambda = (_1778_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1779_lambda));
        }
      } else {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Failure(_System.Tuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>.create(fromType, fromTpe, toType, toTpe, typeParams));
      }
    }
    public bool IsDowncastConversion(RAST._IType fromTpe, RAST._IType toTpe)
    {
      if (((fromTpe).IsObjectOrPointer()) && ((toTpe).IsObjectOrPointer())) {
        return (((fromTpe).ObjectOrPointerUnderlying()).is_DynType) && (!(((toTpe).ObjectOrPointerUnderlying()).is_DynType));
      } else {
        return false;
      }
    }
    public void GenExprConvertOther(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs63 = e;
      DAST._IExpression _1780_expr = _let_tmp_rhs63.dtor_value;
      DAST._IType _1781_fromTpe = _let_tmp_rhs63.dtor_from;
      DAST._IType _1782_toTpe = _let_tmp_rhs63.dtor_typ;
      RAST._IType _1783_fromTpeGen;
      RAST._IType _out268;
      _out268 = (this).GenType(_1781_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1783_fromTpeGen = _out268;
      RAST._IType _1784_toTpeGen;
      RAST._IType _out269;
      _out269 = (this).GenType(_1782_toTpe, DCOMP.GenTypeContext.InBinding());
      _1784_toTpeGen = _out269;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1785_upcastConverter;
      _1785_upcastConverter = (this).UpcastConversionLambda(_1781_fromTpe, _1783_fromTpeGen, _1782_toTpe, _1784_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1785_upcastConverter).is_Success) {
        RAST._IExpr _1786_conversionLambda;
        _1786_conversionLambda = (_1785_upcastConverter).dtor_value;
        RAST._IExpr _1787_recursiveGen;
        DCOMP._IOwnership _1788_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1789_recIdents;
        RAST._IExpr _out270;
        DCOMP._IOwnership _out271;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out272;
        (this).GenExpr(_1780_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out270, out _out271, out _out272);
        _1787_recursiveGen = _out270;
        _1788_recOwned = _out271;
        _1789_recIdents = _out272;
        readIdents = _1789_recIdents;
        r = (_1786_conversionLambda).Apply1(_1787_recursiveGen);
        RAST._IExpr _out273;
        DCOMP._IOwnership _out274;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out273, out _out274);
        r = _out273;
        resultingOwnership = _out274;
      } else if ((this).IsDowncastConversion(_1783_fromTpeGen, _1784_toTpeGen)) {
        RAST._IExpr _1790_recursiveGen;
        DCOMP._IOwnership _1791_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1792_recIdents;
        RAST._IExpr _out275;
        DCOMP._IOwnership _out276;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out277;
        (this).GenExpr(_1780_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out275, out _out276, out _out277);
        _1790_recursiveGen = _out275;
        _1791_recOwned = _out276;
        _1792_recIdents = _out277;
        readIdents = _1792_recIdents;
        _1784_toTpeGen = (_1784_toTpeGen).ObjectOrPointerUnderlying();
        r = ((RAST.__default.dafny__runtime).MSel((this).downcast)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1790_recursiveGen, RAST.Expr.create_ExprFromType(_1784_toTpeGen)));
        RAST._IExpr _out278;
        DCOMP._IOwnership _out279;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out278, out _out279);
        r = _out278;
        resultingOwnership = _out279;
      } else {
        RAST._IExpr _1793_recursiveGen;
        DCOMP._IOwnership _1794_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1795_recIdents;
        RAST._IExpr _out280;
        DCOMP._IOwnership _out281;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out282;
        (this).GenExpr(_1780_expr, selfIdent, env, expectedOwnership, out _out280, out _out281, out _out282);
        _1793_recursiveGen = _out280;
        _1794_recOwned = _out281;
        _1795_recIdents = _out282;
        readIdents = _1795_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs64 = _1785_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs65 = _let_tmp_rhs64.dtor_error;
        DAST._IType _1796_fromType = _let_tmp_rhs65.dtor__0;
        RAST._IType _1797_fromTpeGen = _let_tmp_rhs65.dtor__1;
        DAST._IType _1798_toType = _let_tmp_rhs65.dtor__2;
        RAST._IType _1799_toTpeGen = _let_tmp_rhs65.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1800_m = _let_tmp_rhs65.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1801_msg;
        _1801_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1797_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1799_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1801_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1793_recursiveGen)._ToString(DCOMP.__default.IND), _1801_msg));
        RAST._IExpr _out283;
        DCOMP._IOwnership _out284;
        (this).FromOwnership(r, _1794_recOwned, expectedOwnership, out _out283, out _out284);
        r = _out283;
        resultingOwnership = _out284;
      }
    }
    public void GenExprConvert(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs66 = e;
      DAST._IExpression _1802_expr = _let_tmp_rhs66.dtor_value;
      DAST._IType _1803_fromTpe = _let_tmp_rhs66.dtor_from;
      DAST._IType _1804_toTpe = _let_tmp_rhs66.dtor_typ;
      if (object.Equals(_1803_fromTpe, _1804_toTpe)) {
        RAST._IExpr _1805_recursiveGen;
        DCOMP._IOwnership _1806_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1807_recIdents;
        RAST._IExpr _out285;
        DCOMP._IOwnership _out286;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out287;
        (this).GenExpr(_1802_expr, selfIdent, env, expectedOwnership, out _out285, out _out286, out _out287);
        _1805_recursiveGen = _out285;
        _1806_recOwned = _out286;
        _1807_recIdents = _out287;
        r = _1805_recursiveGen;
        RAST._IExpr _out288;
        DCOMP._IOwnership _out289;
        (this).FromOwnership(r, _1806_recOwned, expectedOwnership, out _out288, out _out289);
        r = _out288;
        resultingOwnership = _out289;
        readIdents = _1807_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source94 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1803_fromTpe, _1804_toTpe);
        bool unmatched94 = true;
        if (unmatched94) {
          DAST._IType _10 = _source94.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1808_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1809_range = kind2.dtor_range;
              bool _1810_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1811_attributes = resolved2.dtor_attributes;
              unmatched94 = false;
              {
                RAST._IExpr _out290;
                DCOMP._IOwnership _out291;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out292;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out290, out _out291, out _out292);
                r = _out290;
                resultingOwnership = _out291;
                readIdents = _out292;
              }
            }
          }
        }
        if (unmatched94) {
          DAST._IType _00 = _source94.dtor__0;
          if (_00.is_UserDefined) {
            DAST._IResolvedType resolved3 = _00.dtor_resolved;
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1812_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1813_range = kind3.dtor_range;
              bool _1814_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1815_attributes = resolved3.dtor_attributes;
              unmatched94 = false;
              {
                RAST._IExpr _out293;
                DCOMP._IOwnership _out294;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out295;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out293, out _out294, out _out295);
                r = _out293;
                resultingOwnership = _out294;
                readIdents = _out295;
              }
            }
          }
        }
        if (unmatched94) {
          DAST._IType _01 = _source94.dtor__0;
          if (_01.is_Primitive) {
            DAST._IPrimitive _h72 = _01.dtor_Primitive_a0;
            if (_h72.is_Int) {
              DAST._IType _11 = _source94.dtor__1;
              if (_11.is_Primitive) {
                DAST._IPrimitive _h73 = _11.dtor_Primitive_a0;
                if (_h73.is_Real) {
                  unmatched94 = false;
                  {
                    RAST._IExpr _1816_recursiveGen;
                    DCOMP._IOwnership _1817___v136;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1818_recIdents;
                    RAST._IExpr _out296;
                    DCOMP._IOwnership _out297;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
                    (this).GenExpr(_1802_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out296, out _out297, out _out298);
                    _1816_recursiveGen = _out296;
                    _1817___v136 = _out297;
                    _1818_recIdents = _out298;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1816_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out299;
                    DCOMP._IOwnership _out300;
                    (this).FromOwned(r, expectedOwnership, out _out299, out _out300);
                    r = _out299;
                    resultingOwnership = _out300;
                    readIdents = _1818_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched94) {
          DAST._IType _02 = _source94.dtor__0;
          if (_02.is_Primitive) {
            DAST._IPrimitive _h74 = _02.dtor_Primitive_a0;
            if (_h74.is_Real) {
              DAST._IType _12 = _source94.dtor__1;
              if (_12.is_Primitive) {
                DAST._IPrimitive _h75 = _12.dtor_Primitive_a0;
                if (_h75.is_Int) {
                  unmatched94 = false;
                  {
                    RAST._IExpr _1819_recursiveGen;
                    DCOMP._IOwnership _1820___v137;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1821_recIdents;
                    RAST._IExpr _out301;
                    DCOMP._IOwnership _out302;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out303;
                    (this).GenExpr(_1802_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out301, out _out302, out _out303);
                    _1819_recursiveGen = _out301;
                    _1820___v137 = _out302;
                    _1821_recIdents = _out303;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1819_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out304;
                    DCOMP._IOwnership _out305;
                    (this).FromOwned(r, expectedOwnership, out _out304, out _out305);
                    r = _out304;
                    resultingOwnership = _out305;
                    readIdents = _1821_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched94) {
          DAST._IType _03 = _source94.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h76 = _03.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _13 = _source94.dtor__1;
              if (_13.is_Passthrough) {
                unmatched94 = false;
                {
                  RAST._IType _1822_rhsType;
                  RAST._IType _out306;
                  _out306 = (this).GenType(_1804_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1822_rhsType = _out306;
                  RAST._IExpr _1823_recursiveGen;
                  DCOMP._IOwnership _1824___v139;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1825_recIdents;
                  RAST._IExpr _out307;
                  DCOMP._IOwnership _out308;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out309;
                  (this).GenExpr(_1802_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out307, out _out308, out _out309);
                  _1823_recursiveGen = _out307;
                  _1824___v139 = _out308;
                  _1825_recIdents = _out309;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1822_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1823_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out310;
                  DCOMP._IOwnership _out311;
                  (this).FromOwned(r, expectedOwnership, out _out310, out _out311);
                  r = _out310;
                  resultingOwnership = _out311;
                  readIdents = _1825_recIdents;
                }
              }
            }
          }
        }
        if (unmatched94) {
          DAST._IType _04 = _source94.dtor__0;
          if (_04.is_Passthrough) {
            DAST._IType _14 = _source94.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h77 = _14.dtor_Primitive_a0;
              if (_h77.is_Int) {
                unmatched94 = false;
                {
                  RAST._IType _1826_rhsType;
                  RAST._IType _out312;
                  _out312 = (this).GenType(_1803_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1826_rhsType = _out312;
                  RAST._IExpr _1827_recursiveGen;
                  DCOMP._IOwnership _1828___v141;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1829_recIdents;
                  RAST._IExpr _out313;
                  DCOMP._IOwnership _out314;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out315;
                  (this).GenExpr(_1802_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out313, out _out314, out _out315);
                  _1827_recursiveGen = _out313;
                  _1828___v141 = _out314;
                  _1829_recIdents = _out315;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1827_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out316;
                  DCOMP._IOwnership _out317;
                  (this).FromOwned(r, expectedOwnership, out _out316, out _out317);
                  r = _out316;
                  resultingOwnership = _out317;
                  readIdents = _1829_recIdents;
                }
              }
            }
          }
        }
        if (unmatched94) {
          DAST._IType _05 = _source94.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h78 = _05.dtor_Primitive_a0;
            if (_h78.is_Int) {
              DAST._IType _15 = _source94.dtor__1;
              if (_15.is_Primitive) {
                DAST._IPrimitive _h79 = _15.dtor_Primitive_a0;
                if (_h79.is_Char) {
                  unmatched94 = false;
                  {
                    RAST._IType _1830_rhsType;
                    RAST._IType _out318;
                    _out318 = (this).GenType(_1804_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1830_rhsType = _out318;
                    RAST._IExpr _1831_recursiveGen;
                    DCOMP._IOwnership _1832___v142;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1833_recIdents;
                    RAST._IExpr _out319;
                    DCOMP._IOwnership _out320;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out321;
                    (this).GenExpr(_1802_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out319, out _out320, out _out321);
                    _1831_recursiveGen = _out319;
                    _1832___v142 = _out320;
                    _1833_recIdents = _out321;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1831_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out322;
                    DCOMP._IOwnership _out323;
                    (this).FromOwned(r, expectedOwnership, out _out322, out _out323);
                    r = _out322;
                    resultingOwnership = _out323;
                    readIdents = _1833_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched94) {
          DAST._IType _06 = _source94.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h710 = _06.dtor_Primitive_a0;
            if (_h710.is_Char) {
              DAST._IType _16 = _source94.dtor__1;
              if (_16.is_Primitive) {
                DAST._IPrimitive _h711 = _16.dtor_Primitive_a0;
                if (_h711.is_Int) {
                  unmatched94 = false;
                  {
                    RAST._IType _1834_rhsType;
                    RAST._IType _out324;
                    _out324 = (this).GenType(_1803_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1834_rhsType = _out324;
                    RAST._IExpr _1835_recursiveGen;
                    DCOMP._IOwnership _1836___v143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1837_recIdents;
                    RAST._IExpr _out325;
                    DCOMP._IOwnership _out326;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out327;
                    (this).GenExpr(_1802_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out325, out _out326, out _out327);
                    _1835_recursiveGen = _out325;
                    _1836___v143 = _out326;
                    _1837_recIdents = _out327;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1835_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out328;
                    DCOMP._IOwnership _out329;
                    (this).FromOwned(r, expectedOwnership, out _out328, out _out329);
                    r = _out328;
                    resultingOwnership = _out329;
                    readIdents = _1837_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched94) {
          DAST._IType _07 = _source94.dtor__0;
          if (_07.is_Passthrough) {
            DAST._IType _17 = _source94.dtor__1;
            if (_17.is_Passthrough) {
              unmatched94 = false;
              {
                RAST._IExpr _1838_recursiveGen;
                DCOMP._IOwnership _1839___v146;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1840_recIdents;
                RAST._IExpr _out330;
                DCOMP._IOwnership _out331;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out332;
                (this).GenExpr(_1802_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out330, out _out331, out _out332);
                _1838_recursiveGen = _out330;
                _1839___v146 = _out331;
                _1840_recIdents = _out332;
                RAST._IType _1841_toTpeGen;
                RAST._IType _out333;
                _out333 = (this).GenType(_1804_toTpe, DCOMP.GenTypeContext.InBinding());
                _1841_toTpeGen = _out333;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1838_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1841_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out334;
                DCOMP._IOwnership _out335;
                (this).FromOwned(r, expectedOwnership, out _out334, out _out335);
                r = _out334;
                resultingOwnership = _out335;
                readIdents = _1840_recIdents;
              }
            }
          }
        }
        if (unmatched94) {
          unmatched94 = false;
          {
            RAST._IExpr _out336;
            DCOMP._IOwnership _out337;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out338;
            (this).GenExprConvertOther(e, selfIdent, env, expectedOwnership, out _out336, out _out337, out _out338);
            r = _out336;
            resultingOwnership = _out337;
            readIdents = _out338;
          }
        }
      }
      return ;
    }
    public void GenIdent(Dafny.ISequence<Dafny.Rune> rName, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      r = RAST.Expr.create_Identifier(rName);
      Std.Wrappers._IOption<RAST._IType> _1842_tpe;
      _1842_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1843_placeboOpt;
      _1843_placeboOpt = (((_1842_tpe).is_Some) ? (((_1842_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1844_currentlyBorrowed;
      _1844_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1845_noNeedOfClone;
      _1845_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1843_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1844_currentlyBorrowed = false;
        _1845_noNeedOfClone = true;
        _1842_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1843_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_1844_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1842_tpe).is_Some) && (((_1842_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1846_needObjectFromRef;
        _1846_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source95 = (selfIdent).dtor_dafnyType;
          bool unmatched95 = true;
          if (unmatched95) {
            if (_source95.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source95.dtor_resolved;
              DAST._IResolvedTypeBase _1847_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1848_attributes = resolved4.dtor_attributes;
              unmatched95 = false;
              return ((_1847_base).is_Class) || ((_1847_base).is_Trait);
            }
          }
          if (unmatched95) {
            unmatched95 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_1846_needObjectFromRef) {
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1845_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1845_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1844_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1842_tpe).is_Some) && (((_1842_tpe).dtor_value).IsPointer())) {
            r = ((this).read__macro).Apply1(r);
          } else {
            r = RAST.__default.Borrow(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      }
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(rName);
      return ;
    }
    public bool HasExternAttributeRenamingModule(Dafny.ISequence<DAST._IAttribute> attributes) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1849_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1849_attributes).UniqueElements, false, (((_exists_var_1) => {
        DAST._IAttribute _1850_attribute = (DAST._IAttribute)_exists_var_1;
        return ((_1849_attributes).Contains(_1850_attribute)) && ((((_1850_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1850_attribute).dtor_args).Count)) == (new BigInteger(2))));
      }))))(attributes);
    }
    public void GenArgs(DCOMP._ISelfInfo selfIdent, DAST._ICallName name, Dafny.ISequence<DAST._IType> typeArgs, Dafny.ISequence<DAST._IExpression> args, DCOMP._IEnvironment env, out Dafny.ISequence<RAST._IExpr> argExprs, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out Dafny.ISequence<RAST._IType> typeExprs, out Std.Wrappers._IOption<DAST._IResolvedType> fullNameQualifier)
    {
      argExprs = Dafny.Sequence<RAST._IExpr>.Empty;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      typeExprs = Dafny.Sequence<RAST._IType>.Empty;
      fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.Default();
      argExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.ISequence<DAST._IFormal> _1851_signature;
      _1851_signature = (((name).is_CallName) ? ((((((name).dtor_receiverArg).is_Some) && ((name).dtor_receiverAsArgument)) ? (Dafny.Sequence<DAST._IFormal>.Concat(Dafny.Sequence<DAST._IFormal>.FromElements(((name).dtor_receiverArg).dtor_value), ((name).dtor_signature))) : (((name).dtor_signature)))) : (Dafny.Sequence<DAST._IFormal>.FromElements()));
      BigInteger _hi38 = new BigInteger((args).Count);
      for (BigInteger _1852_i = BigInteger.Zero; _1852_i < _hi38; _1852_i++) {
        DCOMP._IOwnership _1853_argOwnership;
        _1853_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if ((_1852_i) < (new BigInteger((_1851_signature).Count))) {
          RAST._IType _1854_tpe;
          RAST._IType _out339;
          _out339 = (this).GenType(((_1851_signature).Select(_1852_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1854_tpe = _out339;
          if ((_1854_tpe).CanReadWithoutClone()) {
            _1853_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1855_argExpr;
        DCOMP._IOwnership _1856___v153;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1857_argIdents;
        RAST._IExpr _out340;
        DCOMP._IOwnership _out341;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out342;
        (this).GenExpr((args).Select(_1852_i), selfIdent, env, _1853_argOwnership, out _out340, out _out341, out _out342);
        _1855_argExpr = _out340;
        _1856___v153 = _out341;
        _1857_argIdents = _out342;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1855_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1857_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi39 = new BigInteger((typeArgs).Count);
      for (BigInteger _1858_typeI = BigInteger.Zero; _1858_typeI < _hi39; _1858_typeI++) {
        RAST._IType _1859_typeExpr;
        RAST._IType _out343;
        _out343 = (this).GenType((typeArgs).Select(_1858_typeI), DCOMP.GenTypeContext.@default());
        _1859_typeExpr = _out343;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1859_typeExpr));
      }
      DAST._ICallName _source96 = name;
      bool unmatched96 = true;
      if (unmatched96) {
        if (_source96.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _1860_nameIdent = _source96.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType1 = _source96.dtor_onType;
          if (onType1.is_Some) {
            DAST._IType value10 = onType1.dtor_value;
            if (value10.is_UserDefined) {
              DAST._IResolvedType _1861_resolvedType = value10.dtor_resolved;
              unmatched96 = false;
              if ((((_1861_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_1862_resolvedType, _1863_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(((_1862_resolvedType).dtor_properMethods).UniqueElements, true, (((_forall_var_8) => {
                Dafny.ISequence<Dafny.Rune> _1864_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                return !(((_1862_resolvedType).dtor_properMethods).Contains(_1864_m)) || (!object.Equals((_1864_m), _1863_nameIdent));
              }))))(_1861_resolvedType, _1860_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_1861_resolvedType, (_1860_nameIdent)), _1861_resolvedType));
              } else {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
              }
            }
          }
        }
      }
      if (unmatched96) {
        unmatched96 = false;
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
      if ((((((fullNameQualifier).is_Some) && ((selfIdent).is_ThisTyped)) && (((selfIdent).dtor_dafnyType).is_UserDefined)) && ((this).IsSameResolvedType(((selfIdent).dtor_dafnyType).dtor_resolved, (fullNameQualifier).dtor_value))) && (!((this).HasExternAttributeRenamingModule(((fullNameQualifier).dtor_value).dtor_attributes)))) {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    }
    public Dafny.ISequence<Dafny.Rune> GetMethodName(DAST._IExpression @on, DAST._ICallName name)
    {
      var _pat_let_tv146 = @on;
      DAST._ICallName _source97 = name;
      bool unmatched97 = true;
      if (unmatched97) {
        if (_source97.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _1865_ident = _source97.dtor_name;
          unmatched97 = false;
          if ((_pat_let_tv146).is_ExternCompanion) {
            return (_1865_ident);
          } else {
            return DCOMP.__default.escapeName(_1865_ident);
          }
        }
      }
      if (unmatched97) {
        bool disjunctiveMatch14 = false;
        if (_source97.is_MapBuilderAdd) {
          disjunctiveMatch14 = true;
        }
        if (_source97.is_SetBuilderAdd) {
          disjunctiveMatch14 = true;
        }
        if (disjunctiveMatch14) {
          unmatched97 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
        }
      }
      if (unmatched97) {
        bool disjunctiveMatch15 = false;
        disjunctiveMatch15 = true;
        disjunctiveMatch15 = true;
        if (disjunctiveMatch15) {
          unmatched97 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
        }
      }
      throw new System.Exception("unexpected control point");
    }
    public void GenExpr(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source98 = e;
      bool unmatched98 = true;
      if (unmatched98) {
        if (_source98.is_Literal) {
          unmatched98 = false;
          RAST._IExpr _out344;
          DCOMP._IOwnership _out345;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out346;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out344, out _out345, out _out346);
          r = _out344;
          resultingOwnership = _out345;
          readIdents = _out346;
        }
      }
      if (unmatched98) {
        if (_source98.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1866_name = _source98.dtor_name;
          unmatched98 = false;
          {
            RAST._IExpr _out347;
            DCOMP._IOwnership _out348;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
            (this).GenIdent(DCOMP.__default.escapeVar(_1866_name), selfIdent, env, expectedOwnership, out _out347, out _out348, out _out349);
            r = _out347;
            resultingOwnership = _out348;
            readIdents = _out349;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_ExternCompanion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1867_path = _source98.dtor_ExternCompanion_a0;
          unmatched98 = false;
          {
            RAST._IExpr _out350;
            _out350 = DCOMP.COMP.GenPathExpr(_1867_path, false);
            r = _out350;
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out351;
              DCOMP._IOwnership _out352;
              (this).FromOwned(r, expectedOwnership, out _out351, out _out352);
              r = _out351;
              resultingOwnership = _out352;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1868_path = _source98.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _1869_typeArgs = _source98.dtor_typeArgs;
          unmatched98 = false;
          {
            RAST._IExpr _out353;
            _out353 = DCOMP.COMP.GenPathExpr(_1868_path, true);
            r = _out353;
            if ((new BigInteger((_1869_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1870_typeExprs;
              _1870_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_1869_typeArgs).Count);
              for (BigInteger _1871_i = BigInteger.Zero; _1871_i < _hi40; _1871_i++) {
                RAST._IType _1872_typeExpr;
                RAST._IType _out354;
                _out354 = (this).GenType((_1869_typeArgs).Select(_1871_i), DCOMP.GenTypeContext.@default());
                _1872_typeExpr = _out354;
                _1870_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1870_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1872_typeExpr));
              }
              r = (r).ApplyType(_1870_typeExprs);
            }
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out355;
              DCOMP._IOwnership _out356;
              (this).FromOwned(r, expectedOwnership, out _out355, out _out356);
              r = _out355;
              resultingOwnership = _out356;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_InitializationValue) {
          DAST._IType _1873_typ = _source98.dtor_typ;
          unmatched98 = false;
          {
            RAST._IType _1874_typExpr;
            RAST._IType _out357;
            _out357 = (this).GenType(_1873_typ, DCOMP.GenTypeContext.@default());
            _1874_typExpr = _out357;
            if ((_1874_typExpr).IsObjectOrPointer()) {
              r = (_1874_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1874_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            }
            RAST._IExpr _out358;
            DCOMP._IOwnership _out359;
            (this).FromOwned(r, expectedOwnership, out _out358, out _out359);
            r = _out358;
            resultingOwnership = _out359;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1875_values = _source98.dtor_Tuple_a0;
          unmatched98 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1876_exprs;
            _1876_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi41 = new BigInteger((_1875_values).Count);
            for (BigInteger _1877_i = BigInteger.Zero; _1877_i < _hi41; _1877_i++) {
              RAST._IExpr _1878_recursiveGen;
              DCOMP._IOwnership _1879___v163;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1880_recIdents;
              RAST._IExpr _out360;
              DCOMP._IOwnership _out361;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out362;
              (this).GenExpr((_1875_values).Select(_1877_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out360, out _out361, out _out362);
              _1878_recursiveGen = _out360;
              _1879___v163 = _out361;
              _1880_recIdents = _out362;
              _1876_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1876_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1878_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1880_recIdents);
            }
            r = (((new BigInteger((_1875_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1876_exprs)) : (RAST.__default.SystemTuple(_1876_exprs)));
            RAST._IExpr _out363;
            DCOMP._IOwnership _out364;
            (this).FromOwned(r, expectedOwnership, out _out363, out _out364);
            r = _out363;
            resultingOwnership = _out364;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1881_path = _source98.dtor_path;
          Dafny.ISequence<DAST._IType> _1882_typeArgs = _source98.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1883_args = _source98.dtor_args;
          unmatched98 = false;
          {
            RAST._IExpr _out365;
            _out365 = DCOMP.COMP.GenPathExpr(_1881_path, true);
            r = _out365;
            if ((new BigInteger((_1882_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1884_typeExprs;
              _1884_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi42 = new BigInteger((_1882_typeArgs).Count);
              for (BigInteger _1885_i = BigInteger.Zero; _1885_i < _hi42; _1885_i++) {
                RAST._IType _1886_typeExpr;
                RAST._IType _out366;
                _out366 = (this).GenType((_1882_typeArgs).Select(_1885_i), DCOMP.GenTypeContext.@default());
                _1886_typeExpr = _out366;
                _1884_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1884_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1886_typeExpr));
              }
              r = (r).ApplyType(_1884_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1887_arguments;
            _1887_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi43 = new BigInteger((_1883_args).Count);
            for (BigInteger _1888_i = BigInteger.Zero; _1888_i < _hi43; _1888_i++) {
              RAST._IExpr _1889_recursiveGen;
              DCOMP._IOwnership _1890___v164;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1891_recIdents;
              RAST._IExpr _out367;
              DCOMP._IOwnership _out368;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out369;
              (this).GenExpr((_1883_args).Select(_1888_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out367, out _out368, out _out369);
              _1889_recursiveGen = _out367;
              _1890___v164 = _out368;
              _1891_recIdents = _out369;
              _1887_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1887_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1889_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1891_recIdents);
            }
            r = (r).Apply(_1887_arguments);
            RAST._IExpr _out370;
            DCOMP._IOwnership _out371;
            (this).FromOwned(r, expectedOwnership, out _out370, out _out371);
            r = _out370;
            resultingOwnership = _out371;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _1892_dims = _source98.dtor_dims;
          DAST._IType _1893_typ = _source98.dtor_typ;
          unmatched98 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1892_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1894_msg;
              _1894_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1894_msg);
              }
              r = RAST.Expr.create_RawExpr(_1894_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1895_typeGen;
              RAST._IType _out372;
              _out372 = (this).GenType(_1893_typ, DCOMP.GenTypeContext.@default());
              _1895_typeGen = _out372;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1896_dimExprs;
              _1896_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi44 = new BigInteger((_1892_dims).Count);
              for (BigInteger _1897_i = BigInteger.Zero; _1897_i < _hi44; _1897_i++) {
                RAST._IExpr _1898_recursiveGen;
                DCOMP._IOwnership _1899___v165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1900_recIdents;
                RAST._IExpr _out373;
                DCOMP._IOwnership _out374;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out375;
                (this).GenExpr((_1892_dims).Select(_1897_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out373, out _out374, out _out375);
                _1898_recursiveGen = _out373;
                _1899___v165 = _out374;
                _1900_recIdents = _out375;
                _1896_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1896_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_1898_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1900_recIdents);
              }
              if ((new BigInteger((_1892_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1901_class__name;
                _1901_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1892_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1901_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1895_typeGen))).MSel((this).placebos__usize)).Apply(_1896_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1895_typeGen))).Apply(_1896_dimExprs);
              }
            }
            RAST._IExpr _out376;
            DCOMP._IOwnership _out377;
            (this).FromOwned(r, expectedOwnership, out _out376, out _out377);
            r = _out376;
            resultingOwnership = _out377;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_ArrayIndexToInt) {
          DAST._IExpression _1902_underlying = _source98.dtor_value;
          unmatched98 = false;
          {
            RAST._IExpr _1903_recursiveGen;
            DCOMP._IOwnership _1904___v166;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1905_recIdents;
            RAST._IExpr _out378;
            DCOMP._IOwnership _out379;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out380;
            (this).GenExpr(_1902_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out378, out _out379, out _out380);
            _1903_recursiveGen = _out378;
            _1904___v166 = _out379;
            _1905_recIdents = _out380;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1903_recursiveGen);
            readIdents = _1905_recIdents;
            RAST._IExpr _out381;
            DCOMP._IOwnership _out382;
            (this).FromOwned(r, expectedOwnership, out _out381, out _out382);
            r = _out381;
            resultingOwnership = _out382;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_FinalizeNewArray) {
          DAST._IExpression _1906_underlying = _source98.dtor_value;
          DAST._IType _1907_typ = _source98.dtor_typ;
          unmatched98 = false;
          {
            RAST._IType _1908_tpe;
            RAST._IType _out383;
            _out383 = (this).GenType(_1907_typ, DCOMP.GenTypeContext.@default());
            _1908_tpe = _out383;
            RAST._IExpr _1909_recursiveGen;
            DCOMP._IOwnership _1910___v167;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1911_recIdents;
            RAST._IExpr _out384;
            DCOMP._IOwnership _out385;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out386;
            (this).GenExpr(_1906_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out384, out _out385, out _out386);
            _1909_recursiveGen = _out384;
            _1910___v167 = _out385;
            _1911_recIdents = _out386;
            readIdents = _1911_recIdents;
            if ((_1908_tpe).IsObjectOrPointer()) {
              RAST._IType _1912_t;
              _1912_t = (_1908_tpe).ObjectOrPointerUnderlying();
              if ((_1912_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1909_recursiveGen);
              } else if ((_1912_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1913_c;
                _1913_c = (_1912_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1913_c)).MSel((this).array__construct)).Apply1(_1909_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1908_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1908_tpe)._ToString(DCOMP.__default.IND)));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            }
            RAST._IExpr _out387;
            DCOMP._IOwnership _out388;
            (this).FromOwned(r, expectedOwnership, out _out387, out _out388);
            r = _out387;
            resultingOwnership = _out388;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_DatatypeValue) {
          DAST._IResolvedType _1914_datatypeType = _source98.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1915_typeArgs = _source98.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1916_variant = _source98.dtor_variant;
          bool _1917_isCo = _source98.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1918_values = _source98.dtor_contents;
          unmatched98 = false;
          {
            RAST._IExpr _out389;
            _out389 = DCOMP.COMP.GenPathExpr((_1914_datatypeType).dtor_path, true);
            r = _out389;
            Dafny.ISequence<RAST._IType> _1919_genTypeArgs;
            _1919_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi45 = new BigInteger((_1915_typeArgs).Count);
            for (BigInteger _1920_i = BigInteger.Zero; _1920_i < _hi45; _1920_i++) {
              RAST._IType _1921_typeExpr;
              RAST._IType _out390;
              _out390 = (this).GenType((_1915_typeArgs).Select(_1920_i), DCOMP.GenTypeContext.@default());
              _1921_typeExpr = _out390;
              _1919_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1919_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1921_typeExpr));
            }
            if ((new BigInteger((_1915_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1919_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1916_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1922_assignments;
            _1922_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi46 = new BigInteger((_1918_values).Count);
            for (BigInteger _1923_i = BigInteger.Zero; _1923_i < _hi46; _1923_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs67 = (_1918_values).Select(_1923_i);
              Dafny.ISequence<Dafny.Rune> _1924_name = _let_tmp_rhs67.dtor__0;
              DAST._IExpression _1925_value = _let_tmp_rhs67.dtor__1;
              if (_1917_isCo) {
                RAST._IExpr _1926_recursiveGen;
                DCOMP._IOwnership _1927___v168;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1928_recIdents;
                RAST._IExpr _out391;
                DCOMP._IOwnership _out392;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out393;
                (this).GenExpr(_1925_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out391, out _out392, out _out393);
                _1926_recursiveGen = _out391;
                _1927___v168 = _out392;
                _1928_recIdents = _out393;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1928_recIdents);
                Dafny.ISequence<Dafny.Rune> _1929_allReadCloned;
                _1929_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1928_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1930_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1928_recIdents).Elements) {
                    _1930_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1928_recIdents).Contains(_1930_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4615)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1929_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1929_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1930_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1930_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1928_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1928_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1930_next));
                }
                Dafny.ISequence<Dafny.Rune> _1931_wasAssigned;
                _1931_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1929_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1926_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1922_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1922_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(_1924_name), RAST.Expr.create_RawExpr(_1931_wasAssigned))));
              } else {
                RAST._IExpr _1932_recursiveGen;
                DCOMP._IOwnership _1933___v169;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1934_recIdents;
                RAST._IExpr _out394;
                DCOMP._IOwnership _out395;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out396;
                (this).GenExpr(_1925_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out394, out _out395, out _out396);
                _1932_recursiveGen = _out394;
                _1933___v169 = _out395;
                _1934_recIdents = _out396;
                _1922_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1922_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(_1924_name), _1932_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1934_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1922_assignments);
            if ((this).IsRcWrapped((_1914_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out397;
            DCOMP._IOwnership _out398;
            (this).FromOwned(r, expectedOwnership, out _out397, out _out398);
            r = _out397;
            resultingOwnership = _out398;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Convert) {
          unmatched98 = false;
          {
            RAST._IExpr _out399;
            DCOMP._IOwnership _out400;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out401;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out399, out _out400, out _out401);
            r = _out399;
            resultingOwnership = _out400;
            readIdents = _out401;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_SeqConstruct) {
          DAST._IExpression _1935_length = _source98.dtor_length;
          DAST._IExpression _1936_expr = _source98.dtor_elem;
          unmatched98 = false;
          {
            RAST._IExpr _1937_recursiveGen;
            DCOMP._IOwnership _1938___v173;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1939_recIdents;
            RAST._IExpr _out402;
            DCOMP._IOwnership _out403;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out404;
            (this).GenExpr(_1936_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out402, out _out403, out _out404);
            _1937_recursiveGen = _out402;
            _1938___v173 = _out403;
            _1939_recIdents = _out404;
            RAST._IExpr _1940_lengthGen;
            DCOMP._IOwnership _1941___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1942_lengthIdents;
            RAST._IExpr _out405;
            DCOMP._IOwnership _out406;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out407;
            (this).GenExpr(_1935_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out405, out _out406, out _out407);
            _1940_lengthGen = _out405;
            _1941___v174 = _out406;
            _1942_lengthIdents = _out407;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1937_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1940_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1939_recIdents, _1942_lengthIdents);
            RAST._IExpr _out408;
            DCOMP._IOwnership _out409;
            (this).FromOwned(r, expectedOwnership, out _out408, out _out409);
            r = _out408;
            resultingOwnership = _out409;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1943_exprs = _source98.dtor_elements;
          DAST._IType _1944_typ = _source98.dtor_typ;
          unmatched98 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1945_genTpe;
            RAST._IType _out410;
            _out410 = (this).GenType(_1944_typ, DCOMP.GenTypeContext.@default());
            _1945_genTpe = _out410;
            BigInteger _1946_i;
            _1946_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1947_args;
            _1947_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1946_i) < (new BigInteger((_1943_exprs).Count))) {
              RAST._IExpr _1948_recursiveGen;
              DCOMP._IOwnership _1949___v175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1950_recIdents;
              RAST._IExpr _out411;
              DCOMP._IOwnership _out412;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out413;
              (this).GenExpr((_1943_exprs).Select(_1946_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out411, out _out412, out _out413);
              _1948_recursiveGen = _out411;
              _1949___v175 = _out412;
              _1950_recIdents = _out413;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1950_recIdents);
              _1947_args = Dafny.Sequence<RAST._IExpr>.Concat(_1947_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1948_recursiveGen));
              _1946_i = (_1946_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1947_args);
            if ((new BigInteger((_1947_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1945_genTpe));
            }
            RAST._IExpr _out414;
            DCOMP._IOwnership _out415;
            (this).FromOwned(r, expectedOwnership, out _out414, out _out415);
            r = _out414;
            resultingOwnership = _out415;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1951_exprs = _source98.dtor_elements;
          unmatched98 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1952_generatedValues;
            _1952_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1953_i;
            _1953_i = BigInteger.Zero;
            while ((_1953_i) < (new BigInteger((_1951_exprs).Count))) {
              RAST._IExpr _1954_recursiveGen;
              DCOMP._IOwnership _1955___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1956_recIdents;
              RAST._IExpr _out416;
              DCOMP._IOwnership _out417;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out418;
              (this).GenExpr((_1951_exprs).Select(_1953_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out416, out _out417, out _out418);
              _1954_recursiveGen = _out416;
              _1955___v176 = _out417;
              _1956_recIdents = _out418;
              _1952_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1952_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1954_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1956_recIdents);
              _1953_i = (_1953_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1952_generatedValues);
            RAST._IExpr _out419;
            DCOMP._IOwnership _out420;
            (this).FromOwned(r, expectedOwnership, out _out419, out _out420);
            r = _out419;
            resultingOwnership = _out420;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1957_exprs = _source98.dtor_elements;
          unmatched98 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1958_generatedValues;
            _1958_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1959_i;
            _1959_i = BigInteger.Zero;
            while ((_1959_i) < (new BigInteger((_1957_exprs).Count))) {
              RAST._IExpr _1960_recursiveGen;
              DCOMP._IOwnership _1961___v177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1962_recIdents;
              RAST._IExpr _out421;
              DCOMP._IOwnership _out422;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out423;
              (this).GenExpr((_1957_exprs).Select(_1959_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out421, out _out422, out _out423);
              _1960_recursiveGen = _out421;
              _1961___v177 = _out422;
              _1962_recIdents = _out423;
              _1958_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1958_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1960_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1962_recIdents);
              _1959_i = (_1959_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1958_generatedValues);
            RAST._IExpr _out424;
            DCOMP._IOwnership _out425;
            (this).FromOwned(r, expectedOwnership, out _out424, out _out425);
            r = _out424;
            resultingOwnership = _out425;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_ToMultiset) {
          DAST._IExpression _1963_expr = _source98.dtor_ToMultiset_a0;
          unmatched98 = false;
          {
            RAST._IExpr _1964_recursiveGen;
            DCOMP._IOwnership _1965___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1966_recIdents;
            RAST._IExpr _out426;
            DCOMP._IOwnership _out427;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out428;
            (this).GenExpr(_1963_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out426, out _out427, out _out428);
            _1964_recursiveGen = _out426;
            _1965___v178 = _out427;
            _1966_recIdents = _out428;
            r = ((_1964_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1966_recIdents;
            RAST._IExpr _out429;
            DCOMP._IOwnership _out430;
            (this).FromOwned(r, expectedOwnership, out _out429, out _out430);
            r = _out429;
            resultingOwnership = _out430;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1967_mapElems = _source98.dtor_mapElems;
          unmatched98 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1968_generatedValues;
            _1968_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1969_i;
            _1969_i = BigInteger.Zero;
            while ((_1969_i) < (new BigInteger((_1967_mapElems).Count))) {
              RAST._IExpr _1970_recursiveGenKey;
              DCOMP._IOwnership _1971___v179;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1972_recIdentsKey;
              RAST._IExpr _out431;
              DCOMP._IOwnership _out432;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out433;
              (this).GenExpr(((_1967_mapElems).Select(_1969_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out431, out _out432, out _out433);
              _1970_recursiveGenKey = _out431;
              _1971___v179 = _out432;
              _1972_recIdentsKey = _out433;
              RAST._IExpr _1973_recursiveGenValue;
              DCOMP._IOwnership _1974___v180;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1975_recIdentsValue;
              RAST._IExpr _out434;
              DCOMP._IOwnership _out435;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
              (this).GenExpr(((_1967_mapElems).Select(_1969_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out434, out _out435, out _out436);
              _1973_recursiveGenValue = _out434;
              _1974___v180 = _out435;
              _1975_recIdentsValue = _out436;
              _1968_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1968_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1970_recursiveGenKey, _1973_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1972_recIdentsKey), _1975_recIdentsValue);
              _1969_i = (_1969_i) + (BigInteger.One);
            }
            _1969_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1976_arguments;
            _1976_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1969_i) < (new BigInteger((_1968_generatedValues).Count))) {
              RAST._IExpr _1977_genKey;
              _1977_genKey = ((_1968_generatedValues).Select(_1969_i)).dtor__0;
              RAST._IExpr _1978_genValue;
              _1978_genValue = ((_1968_generatedValues).Select(_1969_i)).dtor__1;
              _1976_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1976_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1977_genKey, _1978_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1969_i = (_1969_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1976_arguments);
            RAST._IExpr _out437;
            DCOMP._IOwnership _out438;
            (this).FromOwned(r, expectedOwnership, out _out437, out _out438);
            r = _out437;
            resultingOwnership = _out438;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_SeqUpdate) {
          DAST._IExpression _1979_expr = _source98.dtor_expr;
          DAST._IExpression _1980_index = _source98.dtor_indexExpr;
          DAST._IExpression _1981_value = _source98.dtor_value;
          unmatched98 = false;
          {
            RAST._IExpr _1982_exprR;
            DCOMP._IOwnership _1983___v181;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1984_exprIdents;
            RAST._IExpr _out439;
            DCOMP._IOwnership _out440;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out441;
            (this).GenExpr(_1979_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out439, out _out440, out _out441);
            _1982_exprR = _out439;
            _1983___v181 = _out440;
            _1984_exprIdents = _out441;
            RAST._IExpr _1985_indexR;
            DCOMP._IOwnership _1986_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1987_indexIdents;
            RAST._IExpr _out442;
            DCOMP._IOwnership _out443;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out444;
            (this).GenExpr(_1980_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out442, out _out443, out _out444);
            _1985_indexR = _out442;
            _1986_indexOwnership = _out443;
            _1987_indexIdents = _out444;
            RAST._IExpr _1988_valueR;
            DCOMP._IOwnership _1989_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1990_valueIdents;
            RAST._IExpr _out445;
            DCOMP._IOwnership _out446;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
            (this).GenExpr(_1981_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out445, out _out446, out _out447);
            _1988_valueR = _out445;
            _1989_valueOwnership = _out446;
            _1990_valueIdents = _out447;
            r = ((_1982_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1985_indexR, _1988_valueR));
            RAST._IExpr _out448;
            DCOMP._IOwnership _out449;
            (this).FromOwned(r, expectedOwnership, out _out448, out _out449);
            r = _out448;
            resultingOwnership = _out449;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1984_exprIdents, _1987_indexIdents), _1990_valueIdents);
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_MapUpdate) {
          DAST._IExpression _1991_expr = _source98.dtor_expr;
          DAST._IExpression _1992_index = _source98.dtor_indexExpr;
          DAST._IExpression _1993_value = _source98.dtor_value;
          unmatched98 = false;
          {
            RAST._IExpr _1994_exprR;
            DCOMP._IOwnership _1995___v182;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1996_exprIdents;
            RAST._IExpr _out450;
            DCOMP._IOwnership _out451;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out452;
            (this).GenExpr(_1991_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out450, out _out451, out _out452);
            _1994_exprR = _out450;
            _1995___v182 = _out451;
            _1996_exprIdents = _out452;
            RAST._IExpr _1997_indexR;
            DCOMP._IOwnership _1998_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1999_indexIdents;
            RAST._IExpr _out453;
            DCOMP._IOwnership _out454;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out455;
            (this).GenExpr(_1992_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out453, out _out454, out _out455);
            _1997_indexR = _out453;
            _1998_indexOwnership = _out454;
            _1999_indexIdents = _out455;
            RAST._IExpr _2000_valueR;
            DCOMP._IOwnership _2001_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2002_valueIdents;
            RAST._IExpr _out456;
            DCOMP._IOwnership _out457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out458;
            (this).GenExpr(_1993_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out456, out _out457, out _out458);
            _2000_valueR = _out456;
            _2001_valueOwnership = _out457;
            _2002_valueIdents = _out458;
            r = ((_1994_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1997_indexR, _2000_valueR));
            RAST._IExpr _out459;
            DCOMP._IOwnership _out460;
            (this).FromOwned(r, expectedOwnership, out _out459, out _out460);
            r = _out459;
            resultingOwnership = _out460;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1996_exprIdents, _1999_indexIdents), _2002_valueIdents);
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_This) {
          unmatched98 = false;
          {
            DCOMP._ISelfInfo _source99 = selfIdent;
            bool unmatched99 = true;
            if (unmatched99) {
              if (_source99.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _2003_id = _source99.dtor_rSelfName;
                DAST._IType _2004_dafnyType = _source99.dtor_dafnyType;
                unmatched99 = false;
                {
                  RAST._IExpr _out461;
                  DCOMP._IOwnership _out462;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out463;
                  (this).GenIdent(_2003_id, selfIdent, env, expectedOwnership, out _out461, out _out462, out _out463);
                  r = _out461;
                  resultingOwnership = _out462;
                  readIdents = _out463;
                }
              }
            }
            if (unmatched99) {
              DCOMP._ISelfInfo _2005_None = _source99;
              unmatched99 = false;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out464;
                DCOMP._IOwnership _out465;
                (this).FromOwned(r, expectedOwnership, out _out464, out _out465);
                r = _out464;
                resultingOwnership = _out465;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Ite) {
          DAST._IExpression _2006_cond = _source98.dtor_cond;
          DAST._IExpression _2007_t = _source98.dtor_thn;
          DAST._IExpression _2008_f = _source98.dtor_els;
          unmatched98 = false;
          {
            RAST._IExpr _2009_cond;
            DCOMP._IOwnership _2010___v183;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2011_recIdentsCond;
            RAST._IExpr _out466;
            DCOMP._IOwnership _out467;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out468;
            (this).GenExpr(_2006_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out466, out _out467, out _out468);
            _2009_cond = _out466;
            _2010___v183 = _out467;
            _2011_recIdentsCond = _out468;
            RAST._IExpr _2012_fExpr;
            DCOMP._IOwnership _2013_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2014_recIdentsF;
            RAST._IExpr _out469;
            DCOMP._IOwnership _out470;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out471;
            (this).GenExpr(_2008_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out469, out _out470, out _out471);
            _2012_fExpr = _out469;
            _2013_fOwned = _out470;
            _2014_recIdentsF = _out471;
            RAST._IExpr _2015_tExpr;
            DCOMP._IOwnership _2016___v184;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2017_recIdentsT;
            RAST._IExpr _out472;
            DCOMP._IOwnership _out473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
            (this).GenExpr(_2007_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out472, out _out473, out _out474);
            _2015_tExpr = _out472;
            _2016___v184 = _out473;
            _2017_recIdentsT = _out474;
            r = RAST.Expr.create_IfExpr(_2009_cond, _2015_tExpr, _2012_fExpr);
            RAST._IExpr _out475;
            DCOMP._IOwnership _out476;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out475, out _out476);
            r = _out475;
            resultingOwnership = _out476;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2011_recIdentsCond, _2017_recIdentsT), _2014_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source98.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _2018_e = _source98.dtor_expr;
            DAST.Format._IUnaryOpFormat _2019_format = _source98.dtor_format1;
            unmatched98 = false;
            {
              RAST._IExpr _2020_recursiveGen;
              DCOMP._IOwnership _2021___v185;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2022_recIdents;
              RAST._IExpr _out477;
              DCOMP._IOwnership _out478;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out479;
              (this).GenExpr(_2018_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out477, out _out478, out _out479);
              _2020_recursiveGen = _out477;
              _2021___v185 = _out478;
              _2022_recIdents = _out479;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _2020_recursiveGen, _2019_format);
              RAST._IExpr _out480;
              DCOMP._IOwnership _out481;
              (this).FromOwned(r, expectedOwnership, out _out480, out _out481);
              r = _out480;
              resultingOwnership = _out481;
              readIdents = _2022_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source98.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _2023_e = _source98.dtor_expr;
            DAST.Format._IUnaryOpFormat _2024_format = _source98.dtor_format1;
            unmatched98 = false;
            {
              RAST._IExpr _2025_recursiveGen;
              DCOMP._IOwnership _2026___v186;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2027_recIdents;
              RAST._IExpr _out482;
              DCOMP._IOwnership _out483;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
              (this).GenExpr(_2023_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out482, out _out483, out _out484);
              _2025_recursiveGen = _out482;
              _2026___v186 = _out483;
              _2027_recIdents = _out484;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _2025_recursiveGen, _2024_format);
              RAST._IExpr _out485;
              DCOMP._IOwnership _out486;
              (this).FromOwned(r, expectedOwnership, out _out485, out _out486);
              r = _out485;
              resultingOwnership = _out486;
              readIdents = _2027_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source98.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _2028_e = _source98.dtor_expr;
            DAST.Format._IUnaryOpFormat _2029_format = _source98.dtor_format1;
            unmatched98 = false;
            {
              RAST._IExpr _2030_recursiveGen;
              DCOMP._IOwnership _2031_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2032_recIdents;
              RAST._IExpr _out487;
              DCOMP._IOwnership _out488;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out489;
              (this).GenExpr(_2028_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out487, out _out488, out _out489);
              _2030_recursiveGen = _out487;
              _2031_recOwned = _out488;
              _2032_recIdents = _out489;
              r = ((_2030_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out490;
              DCOMP._IOwnership _out491;
              (this).FromOwned(r, expectedOwnership, out _out490, out _out491);
              r = _out490;
              resultingOwnership = _out491;
              readIdents = _2032_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_BinOp) {
          unmatched98 = false;
          RAST._IExpr _out492;
          DCOMP._IOwnership _out493;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out494;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out492, out _out493, out _out494);
          r = _out492;
          resultingOwnership = _out493;
          readIdents = _out494;
        }
      }
      if (unmatched98) {
        if (_source98.is_ArrayLen) {
          DAST._IExpression _2033_expr = _source98.dtor_expr;
          DAST._IType _2034_exprType = _source98.dtor_exprType;
          BigInteger _2035_dim = _source98.dtor_dim;
          bool _2036_native = _source98.dtor_native;
          unmatched98 = false;
          {
            RAST._IExpr _2037_recursiveGen;
            DCOMP._IOwnership _2038___v191;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2039_recIdents;
            RAST._IExpr _out495;
            DCOMP._IOwnership _out496;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out497;
            (this).GenExpr(_2033_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out495, out _out496, out _out497);
            _2037_recursiveGen = _out495;
            _2038___v191 = _out496;
            _2039_recIdents = _out497;
            RAST._IType _2040_arrayType;
            RAST._IType _out498;
            _out498 = (this).GenType(_2034_exprType, DCOMP.GenTypeContext.@default());
            _2040_arrayType = _out498;
            if (!((_2040_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2041_msg;
              _2041_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2040_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2041_msg);
              r = RAST.Expr.create_RawExpr(_2041_msg);
            } else {
              RAST._IType _2042_underlying;
              _2042_underlying = (_2040_arrayType).ObjectOrPointerUnderlying();
              if (((_2035_dim).Sign == 0) && ((_2042_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2037_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2035_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2037_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_2037_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_2035_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_2036_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out499;
            DCOMP._IOwnership _out500;
            (this).FromOwned(r, expectedOwnership, out _out499, out _out500);
            r = _out499;
            resultingOwnership = _out500;
            readIdents = _2039_recIdents;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_MapKeys) {
          DAST._IExpression _2043_expr = _source98.dtor_expr;
          unmatched98 = false;
          {
            RAST._IExpr _2044_recursiveGen;
            DCOMP._IOwnership _2045___v192;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2046_recIdents;
            RAST._IExpr _out501;
            DCOMP._IOwnership _out502;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out503;
            (this).GenExpr(_2043_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out501, out _out502, out _out503);
            _2044_recursiveGen = _out501;
            _2045___v192 = _out502;
            _2046_recIdents = _out503;
            readIdents = _2046_recIdents;
            r = ((_2044_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out504;
            DCOMP._IOwnership _out505;
            (this).FromOwned(r, expectedOwnership, out _out504, out _out505);
            r = _out504;
            resultingOwnership = _out505;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_MapValues) {
          DAST._IExpression _2047_expr = _source98.dtor_expr;
          unmatched98 = false;
          {
            RAST._IExpr _2048_recursiveGen;
            DCOMP._IOwnership _2049___v193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2050_recIdents;
            RAST._IExpr _out506;
            DCOMP._IOwnership _out507;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out508;
            (this).GenExpr(_2047_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out506, out _out507, out _out508);
            _2048_recursiveGen = _out506;
            _2049___v193 = _out507;
            _2050_recIdents = _out508;
            readIdents = _2050_recIdents;
            r = ((_2048_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out509;
            DCOMP._IOwnership _out510;
            (this).FromOwned(r, expectedOwnership, out _out509, out _out510);
            r = _out509;
            resultingOwnership = _out510;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_MapItems) {
          DAST._IExpression _2051_expr = _source98.dtor_expr;
          unmatched98 = false;
          {
            RAST._IExpr _2052_recursiveGen;
            DCOMP._IOwnership _2053___v194;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2054_recIdents;
            RAST._IExpr _out511;
            DCOMP._IOwnership _out512;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out513;
            (this).GenExpr(_2051_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out511, out _out512, out _out513);
            _2052_recursiveGen = _out511;
            _2053___v194 = _out512;
            _2054_recIdents = _out513;
            readIdents = _2054_recIdents;
            r = ((_2052_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("items"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out514;
            DCOMP._IOwnership _out515;
            (this).FromOwned(r, expectedOwnership, out _out514, out _out515);
            r = _out514;
            resultingOwnership = _out515;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_SelectFn) {
          DAST._IExpression _2055_on = _source98.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2056_field = _source98.dtor_field;
          bool _2057_isDatatype = _source98.dtor_onDatatype;
          bool _2058_isStatic = _source98.dtor_isStatic;
          bool _2059_isConstant = _source98.dtor_isConstant;
          Dafny.ISequence<DAST._IType> _2060_arguments = _source98.dtor_arguments;
          unmatched98 = false;
          {
            RAST._IExpr _2061_onExpr;
            DCOMP._IOwnership _2062_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2063_recIdents;
            RAST._IExpr _out516;
            DCOMP._IOwnership _out517;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out518;
            (this).GenExpr(_2055_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out516, out _out517, out _out518);
            _2061_onExpr = _out516;
            _2062_onOwned = _out517;
            _2063_recIdents = _out518;
            Dafny.ISequence<Dafny.Rune> _2064_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2065_onString;
            _2065_onString = (_2061_onExpr)._ToString(DCOMP.__default.IND);
            if (_2058_isStatic) {
              DCOMP._IEnvironment _2066_lEnv;
              _2066_lEnv = env;
              Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>> _2067_args;
              _2067_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements();
              _2064_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|");
              BigInteger _hi47 = new BigInteger((_2060_arguments).Count);
              for (BigInteger _2068_i = BigInteger.Zero; _2068_i < _hi47; _2068_i++) {
                if ((_2068_i).Sign == 1) {
                  _2064_s = Dafny.Sequence<Dafny.Rune>.Concat(_2064_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                RAST._IType _2069_ty;
                RAST._IType _out519;
                _out519 = (this).GenType((_2060_arguments).Select(_2068_i), DCOMP.GenTypeContext.@default());
                _2069_ty = _out519;
                RAST._IType _2070_bTy;
                _2070_bTy = RAST.Type.create_Borrowed(_2069_ty);
                Dafny.ISequence<Dafny.Rune> _2071_name;
                _2071_name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), Std.Strings.__default.OfInt(_2068_i));
                _2066_lEnv = (_2066_lEnv).AddAssigned(_2071_name, _2070_bTy);
                _2067_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.Concat(_2067_args, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>.create(_2071_name, _2069_ty)));
                _2064_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2064_s, _2071_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_2070_bTy)._ToString(DCOMP.__default.IND));
              }
              _2064_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2064_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| ")), _2065_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_2056_field)), ((_2059_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("));
              BigInteger _hi48 = new BigInteger((_2067_args).Count);
              for (BigInteger _2072_i = BigInteger.Zero; _2072_i < _hi48; _2072_i++) {
                if ((_2072_i).Sign == 1) {
                  _2064_s = Dafny.Sequence<Dafny.Rune>.Concat(_2064_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType> _let_tmp_rhs68 = (_2067_args).Select(_2072_i);
                Dafny.ISequence<Dafny.Rune> _2073_name = _let_tmp_rhs68.dtor__0;
                RAST._IType _2074_ty = _let_tmp_rhs68.dtor__1;
                RAST._IExpr _2075_rIdent;
                DCOMP._IOwnership _2076___v195;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2077___v196;
                RAST._IExpr _out520;
                DCOMP._IOwnership _out521;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out522;
                (this).GenIdent(_2073_name, selfIdent, _2066_lEnv, (((_2074_ty).CanReadWithoutClone()) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed())), out _out520, out _out521, out _out522);
                _2075_rIdent = _out520;
                _2076___v195 = _out521;
                _2077___v196 = _out522;
                _2064_s = Dafny.Sequence<Dafny.Rune>.Concat(_2064_s, (_2075_rIdent)._ToString(DCOMP.__default.IND));
              }
              _2064_s = Dafny.Sequence<Dafny.Rune>.Concat(_2064_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            } else {
              _2064_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2064_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2064_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2065_onString), ((object.Equals(_2062_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2078_args;
              _2078_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2079_i;
              _2079_i = BigInteger.Zero;
              while ((_2079_i) < (new BigInteger((_2060_arguments).Count))) {
                if ((_2079_i).Sign == 1) {
                  _2078_args = Dafny.Sequence<Dafny.Rune>.Concat(_2078_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2078_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2078_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2079_i));
                _2079_i = (_2079_i) + (BigInteger.One);
              }
              _2064_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2064_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2078_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2064_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2064_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_2056_field)), ((_2059_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2078_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2064_s = Dafny.Sequence<Dafny.Rune>.Concat(_2064_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2064_s = Dafny.Sequence<Dafny.Rune>.Concat(_2064_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2080_typeShape;
            _2080_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2081_i;
            _2081_i = BigInteger.Zero;
            while ((_2081_i) < (new BigInteger((_2060_arguments).Count))) {
              if ((_2081_i).Sign == 1) {
                _2080_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2080_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2080_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2080_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2081_i = (_2081_i) + (BigInteger.One);
            }
            _2080_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2080_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2064_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2064_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2080_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2064_s);
            RAST._IExpr _out523;
            DCOMP._IOwnership _out524;
            (this).FromOwned(r, expectedOwnership, out _out523, out _out524);
            r = _out523;
            resultingOwnership = _out524;
            readIdents = _2063_recIdents;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Select) {
          DAST._IExpression _2082_on = _source98.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2083_field = _source98.dtor_field;
          bool _2084_isConstant = _source98.dtor_isConstant;
          bool _2085_isDatatype = _source98.dtor_onDatatype;
          DAST._IType _2086_fieldType = _source98.dtor_fieldType;
          unmatched98 = false;
          {
            if (((_2082_on).is_Companion) || ((_2082_on).is_ExternCompanion)) {
              RAST._IExpr _2087_onExpr;
              DCOMP._IOwnership _2088_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2089_recIdents;
              RAST._IExpr _out525;
              DCOMP._IOwnership _out526;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out527;
              (this).GenExpr(_2082_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out525, out _out526, out _out527);
              _2087_onExpr = _out525;
              _2088_onOwned = _out526;
              _2089_recIdents = _out527;
              r = ((_2087_onExpr).MSel(DCOMP.__default.escapeName(_2083_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out528;
              DCOMP._IOwnership _out529;
              (this).FromOwned(r, expectedOwnership, out _out528, out _out529);
              r = _out528;
              resultingOwnership = _out529;
              readIdents = _2089_recIdents;
              return ;
            } else if (_2085_isDatatype) {
              RAST._IExpr _2090_onExpr;
              DCOMP._IOwnership _2091_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2092_recIdents;
              RAST._IExpr _out530;
              DCOMP._IOwnership _out531;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out532;
              (this).GenExpr(_2082_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out530, out _out531, out _out532);
              _2090_onExpr = _out530;
              _2091_onOwned = _out531;
              _2092_recIdents = _out532;
              r = ((_2090_onExpr).Sel(DCOMP.__default.escapeName(_2083_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2093_typ;
              RAST._IType _out533;
              _out533 = (this).GenType(_2086_fieldType, DCOMP.GenTypeContext.@default());
              _2093_typ = _out533;
              RAST._IExpr _out534;
              DCOMP._IOwnership _out535;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out534, out _out535);
              r = _out534;
              resultingOwnership = _out535;
              readIdents = _2092_recIdents;
            } else {
              RAST._IExpr _2094_onExpr;
              DCOMP._IOwnership _2095_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2096_recIdents;
              RAST._IExpr _out536;
              DCOMP._IOwnership _out537;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
              (this).GenExpr(_2082_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out536, out _out537, out _out538);
              _2094_onExpr = _out536;
              _2095_onOwned = _out537;
              _2096_recIdents = _out538;
              r = _2094_onExpr;
              if (!object.Equals(_2094_onExpr, RAST.__default.self)) {
                RAST._IExpr _source100 = _2094_onExpr;
                bool unmatched100 = true;
                if (unmatched100) {
                  if (_source100.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source100.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source100.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name13 = underlying5.dtor_name;
                        if (object.Equals(name13, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          unmatched100 = false;
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                        }
                      }
                    }
                  }
                }
                if (unmatched100) {
                  unmatched100 = false;
                }
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeName(_2083_field));
              if (_2084_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out539;
              DCOMP._IOwnership _out540;
              (this).FromOwned(r, expectedOwnership, out _out539, out _out540);
              r = _out539;
              resultingOwnership = _out540;
              readIdents = _2096_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Index) {
          DAST._IExpression _2097_on = _source98.dtor_expr;
          DAST._ICollKind _2098_collKind = _source98.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2099_indices = _source98.dtor_indices;
          unmatched98 = false;
          {
            RAST._IExpr _2100_onExpr;
            DCOMP._IOwnership _2101_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2102_recIdents;
            RAST._IExpr _out541;
            DCOMP._IOwnership _out542;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out543;
            (this).GenExpr(_2097_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out541, out _out542, out _out543);
            _2100_onExpr = _out541;
            _2101_onOwned = _out542;
            _2102_recIdents = _out543;
            readIdents = _2102_recIdents;
            r = _2100_onExpr;
            bool _2103_hadArray;
            _2103_hadArray = false;
            if (object.Equals(_2098_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2103_hadArray = true;
              if ((new BigInteger((_2099_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi49 = new BigInteger((_2099_indices).Count);
            for (BigInteger _2104_i = BigInteger.Zero; _2104_i < _hi49; _2104_i++) {
              if (object.Equals(_2098_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2105_idx;
                DCOMP._IOwnership _2106_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2107_recIdentsIdx;
                RAST._IExpr _out544;
                DCOMP._IOwnership _out545;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out546;
                (this).GenExpr((_2099_indices).Select(_2104_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out544, out _out545, out _out546);
                _2105_idx = _out544;
                _2106_idxOwned = _out545;
                _2107_recIdentsIdx = _out546;
                _2105_idx = RAST.__default.IntoUsize(_2105_idx);
                r = RAST.Expr.create_SelectIndex(r, _2105_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2107_recIdentsIdx);
              } else {
                RAST._IExpr _2108_idx;
                DCOMP._IOwnership _2109_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2110_recIdentsIdx;
                RAST._IExpr _out547;
                DCOMP._IOwnership _out548;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
                (this).GenExpr((_2099_indices).Select(_2104_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out547, out _out548, out _out549);
                _2108_idx = _out547;
                _2109_idxOwned = _out548;
                _2110_recIdentsIdx = _out549;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2108_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2110_recIdentsIdx);
              }
            }
            if (_2103_hadArray) {
              r = (r).Clone();
            }
            RAST._IExpr _out550;
            DCOMP._IOwnership _out551;
            (this).FromOwned(r, expectedOwnership, out _out550, out _out551);
            r = _out550;
            resultingOwnership = _out551;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_IndexRange) {
          DAST._IExpression _2111_on = _source98.dtor_expr;
          bool _2112_isArray = _source98.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2113_low = _source98.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2114_high = _source98.dtor_high;
          unmatched98 = false;
          {
            RAST._IExpr _2115_onExpr;
            DCOMP._IOwnership _2116_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2117_recIdents;
            RAST._IExpr _out552;
            DCOMP._IOwnership _out553;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out554;
            (this).GenExpr(_2111_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out552, out _out553, out _out554);
            _2115_onExpr = _out552;
            _2116_onOwned = _out553;
            _2117_recIdents = _out554;
            readIdents = _2117_recIdents;
            Dafny.ISequence<Dafny.Rune> _2118_methodName;
            _2118_methodName = (((_2113_low).is_Some) ? ((((_2114_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2114_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2119_arguments;
            _2119_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source101 = _2113_low;
            bool unmatched101 = true;
            if (unmatched101) {
              if (_source101.is_Some) {
                DAST._IExpression _2120_l = _source101.dtor_value;
                unmatched101 = false;
                {
                  RAST._IExpr _2121_lExpr;
                  DCOMP._IOwnership _2122___v199;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2123_recIdentsL;
                  RAST._IExpr _out555;
                  DCOMP._IOwnership _out556;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
                  (this).GenExpr(_2120_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out555, out _out556, out _out557);
                  _2121_lExpr = _out555;
                  _2122___v199 = _out556;
                  _2123_recIdentsL = _out557;
                  _2119_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2119_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2121_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2123_recIdentsL);
                }
              }
            }
            if (unmatched101) {
              unmatched101 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source102 = _2114_high;
            bool unmatched102 = true;
            if (unmatched102) {
              if (_source102.is_Some) {
                DAST._IExpression _2124_h = _source102.dtor_value;
                unmatched102 = false;
                {
                  RAST._IExpr _2125_hExpr;
                  DCOMP._IOwnership _2126___v200;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2127_recIdentsH;
                  RAST._IExpr _out558;
                  DCOMP._IOwnership _out559;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
                  (this).GenExpr(_2124_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out558, out _out559, out _out560);
                  _2125_hExpr = _out558;
                  _2126___v200 = _out559;
                  _2127_recIdentsH = _out560;
                  _2119_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2119_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2125_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2127_recIdentsH);
                }
              }
            }
            if (unmatched102) {
              unmatched102 = false;
            }
            r = _2115_onExpr;
            if (_2112_isArray) {
              if (!(_2118_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2118_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2118_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2118_methodName))).Apply(_2119_arguments);
            } else {
              if (!(_2118_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2118_methodName)).Apply(_2119_arguments);
              }
            }
            RAST._IExpr _out561;
            DCOMP._IOwnership _out562;
            (this).FromOwned(r, expectedOwnership, out _out561, out _out562);
            r = _out561;
            resultingOwnership = _out562;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_TupleSelect) {
          DAST._IExpression _2128_on = _source98.dtor_expr;
          BigInteger _2129_idx = _source98.dtor_index;
          DAST._IType _2130_fieldType = _source98.dtor_fieldType;
          unmatched98 = false;
          {
            RAST._IExpr _2131_onExpr;
            DCOMP._IOwnership _2132_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2133_recIdents;
            RAST._IExpr _out563;
            DCOMP._IOwnership _out564;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
            (this).GenExpr(_2128_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out563, out _out564, out _out565);
            _2131_onExpr = _out563;
            _2132_onOwnership = _out564;
            _2133_recIdents = _out565;
            Dafny.ISequence<Dafny.Rune> _2134_selName;
            _2134_selName = Std.Strings.__default.OfNat(_2129_idx);
            DAST._IType _source103 = _2130_fieldType;
            bool unmatched103 = true;
            if (unmatched103) {
              if (_source103.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2135_tps = _source103.dtor_Tuple_a0;
                unmatched103 = false;
                if (((_2130_fieldType).is_Tuple) && ((new BigInteger((_2135_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2134_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2134_selName);
                }
              }
            }
            if (unmatched103) {
              unmatched103 = false;
            }
            r = ((_2131_onExpr).Sel(_2134_selName)).Clone();
            RAST._IExpr _out566;
            DCOMP._IOwnership _out567;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out566, out _out567);
            r = _out566;
            resultingOwnership = _out567;
            readIdents = _2133_recIdents;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Call) {
          DAST._IExpression _2136_on = _source98.dtor_on;
          DAST._ICallName _2137_name = _source98.dtor_callName;
          Dafny.ISequence<DAST._IType> _2138_typeArgs = _source98.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2139_args = _source98.dtor_args;
          unmatched98 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2140_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2141_recIdents;
            Dafny.ISequence<RAST._IType> _2142_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2143_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out568;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out569;
            Dafny.ISequence<RAST._IType> _out570;
            Std.Wrappers._IOption<DAST._IResolvedType> _out571;
            (this).GenArgs(selfIdent, _2137_name, _2138_typeArgs, _2139_args, env, out _out568, out _out569, out _out570, out _out571);
            _2140_argExprs = _out568;
            _2141_recIdents = _out569;
            _2142_typeExprs = _out570;
            _2143_fullNameQualifier = _out571;
            readIdents = _2141_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source104 = _2143_fullNameQualifier;
            bool unmatched104 = true;
            if (unmatched104) {
              if (_source104.is_Some) {
                DAST._IResolvedType value11 = _source104.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2144_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2145_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2146_base = value11.dtor_kind;
                unmatched104 = false;
                RAST._IExpr _2147_fullPath;
                RAST._IExpr _out572;
                _out572 = DCOMP.COMP.GenPathExpr(_2144_path, true);
                _2147_fullPath = _out572;
                Dafny.ISequence<RAST._IType> _2148_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out573;
                _out573 = (this).GenTypeArgs(_2145_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2148_onTypeExprs = _out573;
                RAST._IExpr _2149_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2150_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2151_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2146_base).is_Trait) || ((_2146_base).is_Class)) {
                  RAST._IExpr _out574;
                  DCOMP._IOwnership _out575;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out576;
                  (this).GenExpr(_2136_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out574, out _out575, out _out576);
                  _2149_onExpr = _out574;
                  _2150_recOwnership = _out575;
                  _2151_recIdents = _out576;
                  _2149_onExpr = ((this).read__macro).Apply1(_2149_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2151_recIdents);
                } else {
                  RAST._IExpr _out577;
                  DCOMP._IOwnership _out578;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out579;
                  (this).GenExpr(_2136_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out577, out _out578, out _out579);
                  _2149_onExpr = _out577;
                  _2150_recOwnership = _out578;
                  _2151_recIdents = _out579;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2151_recIdents);
                }
                r = ((((_2147_fullPath).ApplyType(_2148_onTypeExprs)).MSel(DCOMP.__default.escapeName((_2137_name).dtor_name))).ApplyType(_2142_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2149_onExpr), _2140_argExprs));
                RAST._IExpr _out580;
                DCOMP._IOwnership _out581;
                (this).FromOwned(r, expectedOwnership, out _out580, out _out581);
                r = _out580;
                resultingOwnership = _out581;
              }
            }
            if (unmatched104) {
              unmatched104 = false;
              RAST._IExpr _2152_onExpr;
              DCOMP._IOwnership _2153___v206;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2154_recIdents;
              RAST._IExpr _out582;
              DCOMP._IOwnership _out583;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out584;
              (this).GenExpr(_2136_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out582, out _out583, out _out584);
              _2152_onExpr = _out582;
              _2153___v206 = _out583;
              _2154_recIdents = _out584;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2154_recIdents);
              Dafny.ISequence<Dafny.Rune> _2155_renderedName;
              _2155_renderedName = (this).GetMethodName(_2136_on, _2137_name);
              DAST._IExpression _source105 = _2136_on;
              bool unmatched105 = true;
              if (unmatched105) {
                bool disjunctiveMatch16 = false;
                if (_source105.is_Companion) {
                  disjunctiveMatch16 = true;
                }
                if (_source105.is_ExternCompanion) {
                  disjunctiveMatch16 = true;
                }
                if (disjunctiveMatch16) {
                  unmatched105 = false;
                  {
                    _2152_onExpr = (_2152_onExpr).MSel(_2155_renderedName);
                  }
                }
              }
              if (unmatched105) {
                unmatched105 = false;
                {
                  if (!object.Equals(_2152_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source106 = _2137_name;
                    bool unmatched106 = true;
                    if (unmatched106) {
                      if (_source106.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source106.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2156_tpe = onType2.dtor_value;
                          unmatched106 = false;
                          RAST._IType _2157_typ;
                          RAST._IType _out585;
                          _out585 = (this).GenType(_2156_tpe, DCOMP.GenTypeContext.@default());
                          _2157_typ = _out585;
                          if ((_2157_typ).IsObjectOrPointer()) {
                            _2152_onExpr = ((this).read__macro).Apply1(_2152_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched106) {
                      unmatched106 = false;
                    }
                  }
                  _2152_onExpr = (_2152_onExpr).Sel(_2155_renderedName);
                }
              }
              r = ((_2152_onExpr).ApplyType(_2142_typeExprs)).Apply(_2140_argExprs);
              RAST._IExpr _out586;
              DCOMP._IOwnership _out587;
              (this).FromOwned(r, expectedOwnership, out _out586, out _out587);
              r = _out586;
              resultingOwnership = _out587;
              return ;
            }
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2158_paramsDafny = _source98.dtor_params;
          DAST._IType _2159_retType = _source98.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2160_body = _source98.dtor_body;
          unmatched98 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2161_params;
            Dafny.ISequence<RAST._IFormal> _out588;
            _out588 = (this).GenParams(_2158_paramsDafny, true);
            _2161_params = _out588;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2162_paramNames;
            _2162_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2163_paramTypesMap;
            _2163_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi50 = new BigInteger((_2161_params).Count);
            for (BigInteger _2164_i = BigInteger.Zero; _2164_i < _hi50; _2164_i++) {
              Dafny.ISequence<Dafny.Rune> _2165_name;
              _2165_name = ((_2161_params).Select(_2164_i)).dtor_name;
              _2162_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2162_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2165_name));
              _2163_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2163_paramTypesMap, _2165_name, ((_2161_params).Select(_2164_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2166_subEnv;
            _2166_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2162_paramNames, _2163_paramTypesMap));
            RAST._IExpr _2167_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2168_recIdents;
            DCOMP._IEnvironment _2169___v216;
            RAST._IExpr _out589;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out590;
            DCOMP._IEnvironment _out591;
            (this).GenStmts(_2160_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2166_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out589, out _out590, out _out591);
            _2167_recursiveGen = _out589;
            _2168_recIdents = _out590;
            _2169___v216 = _out591;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2168_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2168_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2170_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll7 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_7 in (_2170_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2171_name = (Dafny.ISequence<Dafny.Rune>)_compr_7;
                if ((_2170_paramNames).Contains(_2171_name)) {
                  _coll7.Add(_2171_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll7);
            }))())(_2162_paramNames));
            RAST._IExpr _2172_allReadCloned;
            _2172_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2168_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2173_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2168_recIdents).Elements) {
                _2173_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_2168_recIdents).Contains(_2173_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 5117)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2173_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2174_selfCloned;
                DCOMP._IOwnership _2175___v217;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2176___v218;
                RAST._IExpr _out592;
                DCOMP._IOwnership _out593;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out592, out _out593, out _out594);
                _2174_selfCloned = _out592;
                _2175___v217 = _out593;
                _2176___v218 = _out594;
                _2172_allReadCloned = (_2172_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2174_selfCloned)));
              } else if (!((_2162_paramNames).Contains(_2173_next))) {
                RAST._IExpr _2177_copy;
                _2177_copy = (RAST.Expr.create_Identifier(_2173_next)).Clone();
                _2172_allReadCloned = (_2172_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2173_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2177_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2173_next));
              }
              _2168_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2168_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2173_next));
            }
            RAST._IType _2178_retTypeGen;
            RAST._IType _out595;
            _out595 = (this).GenType(_2159_retType, DCOMP.GenTypeContext.InFn());
            _2178_retTypeGen = _out595;
            r = RAST.Expr.create_Block((_2172_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2161_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2178_retTypeGen), RAST.Expr.create_Block(_2167_recursiveGen)))));
            RAST._IExpr _out596;
            DCOMP._IOwnership _out597;
            (this).FromOwned(r, expectedOwnership, out _out596, out _out597);
            r = _out596;
            resultingOwnership = _out597;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2179_values = _source98.dtor_values;
          DAST._IType _2180_retType = _source98.dtor_retType;
          DAST._IExpression _2181_expr = _source98.dtor_expr;
          unmatched98 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2182_paramNames;
            _2182_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2183_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out598;
            _out598 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2184_value) => {
              return (_2184_value).dtor__0;
            })), _2179_values), false);
            _2183_paramFormals = _out598;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2185_paramTypes;
            _2185_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2186_paramNamesSet;
            _2186_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi51 = new BigInteger((_2179_values).Count);
            for (BigInteger _2187_i = BigInteger.Zero; _2187_i < _hi51; _2187_i++) {
              Dafny.ISequence<Dafny.Rune> _2188_name;
              _2188_name = (((_2179_values).Select(_2187_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2189_rName;
              _2189_rName = DCOMP.__default.escapeVar(_2188_name);
              _2182_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2182_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2189_rName));
              _2185_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2185_paramTypes, _2189_rName, ((_2183_paramFormals).Select(_2187_i)).dtor_tpe);
              _2186_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2186_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2189_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi52 = new BigInteger((_2179_values).Count);
            for (BigInteger _2190_i = BigInteger.Zero; _2190_i < _hi52; _2190_i++) {
              RAST._IType _2191_typeGen;
              RAST._IType _out599;
              _out599 = (this).GenType((((_2179_values).Select(_2190_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2191_typeGen = _out599;
              RAST._IExpr _2192_valueGen;
              DCOMP._IOwnership _2193___v219;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2194_recIdents;
              RAST._IExpr _out600;
              DCOMP._IOwnership _out601;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out602;
              (this).GenExpr(((_2179_values).Select(_2190_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out600, out _out601, out _out602);
              _2192_valueGen = _out600;
              _2193___v219 = _out601;
              _2194_recIdents = _out602;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar((((_2179_values).Select(_2190_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2191_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2192_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2194_recIdents);
            }
            DCOMP._IEnvironment _2195_newEnv;
            _2195_newEnv = DCOMP.Environment.create(_2182_paramNames, _2185_paramTypes);
            RAST._IExpr _2196_recGen;
            DCOMP._IOwnership _2197_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2198_recIdents;
            RAST._IExpr _out603;
            DCOMP._IOwnership _out604;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out605;
            (this).GenExpr(_2181_expr, selfIdent, _2195_newEnv, expectedOwnership, out _out603, out _out604, out _out605);
            _2196_recGen = _out603;
            _2197_recOwned = _out604;
            _2198_recIdents = _out605;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2198_recIdents, _2186_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2196_recGen));
            RAST._IExpr _out606;
            DCOMP._IOwnership _out607;
            (this).FromOwnership(r, _2197_recOwned, expectedOwnership, out _out606, out _out607);
            r = _out606;
            resultingOwnership = _out607;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2199_name = _source98.dtor_ident;
          DAST._IType _2200_tpe = _source98.dtor_typ;
          DAST._IExpression _2201_value = _source98.dtor_value;
          DAST._IExpression _2202_iifeBody = _source98.dtor_iifeBody;
          unmatched98 = false;
          {
            RAST._IExpr _2203_valueGen;
            DCOMP._IOwnership _2204___v220;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2205_recIdents;
            RAST._IExpr _out608;
            DCOMP._IOwnership _out609;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
            (this).GenExpr(_2201_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out608, out _out609, out _out610);
            _2203_valueGen = _out608;
            _2204___v220 = _out609;
            _2205_recIdents = _out610;
            readIdents = _2205_recIdents;
            RAST._IType _2206_valueTypeGen;
            RAST._IType _out611;
            _out611 = (this).GenType(_2200_tpe, DCOMP.GenTypeContext.InFn());
            _2206_valueTypeGen = _out611;
            RAST._IExpr _2207_bodyGen;
            DCOMP._IOwnership _2208___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2209_bodyIdents;
            RAST._IExpr _out612;
            DCOMP._IOwnership _out613;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out614;
            (this).GenExpr(_2202_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out612, out _out613, out _out614);
            _2207_bodyGen = _out612;
            _2208___v221 = _out613;
            _2209_bodyIdents = _out614;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2209_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar((_2199_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar((_2199_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_2206_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2203_valueGen))).Then(_2207_bodyGen));
            RAST._IExpr _out615;
            DCOMP._IOwnership _out616;
            (this).FromOwned(r, expectedOwnership, out _out615, out _out616);
            r = _out615;
            resultingOwnership = _out616;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Apply) {
          DAST._IExpression _2210_func = _source98.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2211_args = _source98.dtor_args;
          unmatched98 = false;
          {
            RAST._IExpr _2212_funcExpr;
            DCOMP._IOwnership _2213___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2214_recIdents;
            RAST._IExpr _out617;
            DCOMP._IOwnership _out618;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out619;
            (this).GenExpr(_2210_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out617, out _out618, out _out619);
            _2212_funcExpr = _out617;
            _2213___v222 = _out618;
            _2214_recIdents = _out619;
            readIdents = _2214_recIdents;
            Dafny.ISequence<RAST._IExpr> _2215_rArgs;
            _2215_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi53 = new BigInteger((_2211_args).Count);
            for (BigInteger _2216_i = BigInteger.Zero; _2216_i < _hi53; _2216_i++) {
              RAST._IExpr _2217_argExpr;
              DCOMP._IOwnership _2218_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2219_argIdents;
              RAST._IExpr _out620;
              DCOMP._IOwnership _out621;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
              (this).GenExpr((_2211_args).Select(_2216_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out620, out _out621, out _out622);
              _2217_argExpr = _out620;
              _2218_argOwned = _out621;
              _2219_argIdents = _out622;
              _2215_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2215_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2217_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2219_argIdents);
            }
            r = (_2212_funcExpr).Apply(_2215_rArgs);
            RAST._IExpr _out623;
            DCOMP._IOwnership _out624;
            (this).FromOwned(r, expectedOwnership, out _out623, out _out624);
            r = _out623;
            resultingOwnership = _out624;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_TypeTest) {
          DAST._IExpression _2220_on = _source98.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2221_dType = _source98.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2222_variant = _source98.dtor_variant;
          unmatched98 = false;
          {
            RAST._IExpr _2223_exprGen;
            DCOMP._IOwnership _2224___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2225_recIdents;
            RAST._IExpr _out625;
            DCOMP._IOwnership _out626;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out627;
            (this).GenExpr(_2220_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out625, out _out626, out _out627);
            _2223_exprGen = _out625;
            _2224___v223 = _out626;
            _2225_recIdents = _out627;
            RAST._IType _2226_dTypePath;
            RAST._IType _out628;
            _out628 = DCOMP.COMP.GenPath(_2221_dType);
            _2226_dTypePath = _out628;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2223_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2226_dTypePath).MSel(DCOMP.__default.escapeName(_2222_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out629;
            DCOMP._IOwnership _out630;
            (this).FromOwned(r, expectedOwnership, out _out629, out _out630);
            r = _out629;
            resultingOwnership = _out630;
            readIdents = _2225_recIdents;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Is) {
          DAST._IExpression _2227_expr = _source98.dtor_expr;
          DAST._IType _2228_fromType = _source98.dtor_fromType;
          DAST._IType _2229_toType = _source98.dtor_toType;
          unmatched98 = false;
          {
            RAST._IExpr _2230_expr;
            DCOMP._IOwnership _2231_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2232_recIdents;
            RAST._IExpr _out631;
            DCOMP._IOwnership _out632;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out633;
            (this).GenExpr(_2227_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out631, out _out632, out _out633);
            _2230_expr = _out631;
            _2231_recOwned = _out632;
            _2232_recIdents = _out633;
            RAST._IType _2233_fromType;
            RAST._IType _out634;
            _out634 = (this).GenType(_2228_fromType, DCOMP.GenTypeContext.@default());
            _2233_fromType = _out634;
            RAST._IType _2234_toType;
            RAST._IType _out635;
            _out635 = (this).GenType(_2229_toType, DCOMP.GenTypeContext.@default());
            _2234_toType = _out635;
            if (((_2233_fromType).IsObject()) && ((_2234_toType).IsObject())) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is_instance_of_object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((_2233_fromType).ObjectOrPointerUnderlying(), (_2234_toType).ObjectOrPointerUnderlying()))).Apply1(_2230_expr);
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Source and/or target types of type test is/are not Object"));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
            RAST._IExpr _out636;
            DCOMP._IOwnership _out637;
            (this).FromOwnership(r, _2231_recOwned, expectedOwnership, out _out636, out _out637);
            r = _out636;
            resultingOwnership = _out637;
            readIdents = _2232_recIdents;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_BoolBoundedPool) {
          unmatched98 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out638;
            DCOMP._IOwnership _out639;
            (this).FromOwned(r, expectedOwnership, out _out638, out _out639);
            r = _out638;
            resultingOwnership = _out639;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_SetBoundedPool) {
          DAST._IExpression _2235_of = _source98.dtor_of;
          unmatched98 = false;
          {
            RAST._IExpr _2236_exprGen;
            DCOMP._IOwnership _2237___v224;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2238_recIdents;
            RAST._IExpr _out640;
            DCOMP._IOwnership _out641;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out642;
            (this).GenExpr(_2235_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out640, out _out641, out _out642);
            _2236_exprGen = _out640;
            _2237___v224 = _out641;
            _2238_recIdents = _out642;
            r = ((_2236_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            (this).FromOwned(r, expectedOwnership, out _out643, out _out644);
            r = _out643;
            resultingOwnership = _out644;
            readIdents = _2238_recIdents;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_SeqBoundedPool) {
          DAST._IExpression _2239_of = _source98.dtor_of;
          bool _2240_includeDuplicates = _source98.dtor_includeDuplicates;
          unmatched98 = false;
          {
            RAST._IExpr _2241_exprGen;
            DCOMP._IOwnership _2242___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2243_recIdents;
            RAST._IExpr _out645;
            DCOMP._IOwnership _out646;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out647;
            (this).GenExpr(_2239_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out645, out _out646, out _out647);
            _2241_exprGen = _out645;
            _2242___v225 = _out646;
            _2243_recIdents = _out647;
            r = ((_2241_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2240_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out648;
            DCOMP._IOwnership _out649;
            (this).FromOwned(r, expectedOwnership, out _out648, out _out649);
            r = _out648;
            resultingOwnership = _out649;
            readIdents = _2243_recIdents;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_MapBoundedPool) {
          DAST._IExpression _2244_of = _source98.dtor_of;
          unmatched98 = false;
          {
            RAST._IExpr _2245_exprGen;
            DCOMP._IOwnership _2246___v226;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2247_recIdents;
            RAST._IExpr _out650;
            DCOMP._IOwnership _out651;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out652;
            (this).GenExpr(_2244_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out650, out _out651, out _out652);
            _2245_exprGen = _out650;
            _2246___v226 = _out651;
            _2247_recIdents = _out652;
            r = ((((_2245_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2247_recIdents;
            RAST._IExpr _out653;
            DCOMP._IOwnership _out654;
            (this).FromOwned(r, expectedOwnership, out _out653, out _out654);
            r = _out653;
            resultingOwnership = _out654;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_IntRange) {
          DAST._IExpression _2248_lo = _source98.dtor_lo;
          DAST._IExpression _2249_hi = _source98.dtor_hi;
          bool _2250_up = _source98.dtor_up;
          unmatched98 = false;
          {
            RAST._IExpr _2251_lo;
            DCOMP._IOwnership _2252___v227;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2253_recIdentsLo;
            RAST._IExpr _out655;
            DCOMP._IOwnership _out656;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out657;
            (this).GenExpr(_2248_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out655, out _out656, out _out657);
            _2251_lo = _out655;
            _2252___v227 = _out656;
            _2253_recIdentsLo = _out657;
            RAST._IExpr _2254_hi;
            DCOMP._IOwnership _2255___v228;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2256_recIdentsHi;
            RAST._IExpr _out658;
            DCOMP._IOwnership _out659;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out660;
            (this).GenExpr(_2249_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out658, out _out659, out _out660);
            _2254_hi = _out658;
            _2255___v228 = _out659;
            _2256_recIdentsHi = _out660;
            if (_2250_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2251_lo, _2254_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2254_hi, _2251_lo));
            }
            RAST._IExpr _out661;
            DCOMP._IOwnership _out662;
            (this).FromOwned(r, expectedOwnership, out _out661, out _out662);
            r = _out661;
            resultingOwnership = _out662;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2253_recIdentsLo, _2256_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_UnboundedIntRange) {
          DAST._IExpression _2257_start = _source98.dtor_start;
          bool _2258_up = _source98.dtor_up;
          unmatched98 = false;
          {
            RAST._IExpr _2259_start;
            DCOMP._IOwnership _2260___v229;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2261_recIdentStart;
            RAST._IExpr _out663;
            DCOMP._IOwnership _out664;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out665;
            (this).GenExpr(_2257_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out663, out _out664, out _out665);
            _2259_start = _out663;
            _2260___v229 = _out664;
            _2261_recIdentStart = _out665;
            if (_2258_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2259_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2259_start);
            }
            RAST._IExpr _out666;
            DCOMP._IOwnership _out667;
            (this).FromOwned(r, expectedOwnership, out _out666, out _out667);
            r = _out666;
            resultingOwnership = _out667;
            readIdents = _2261_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_MapBuilder) {
          DAST._IType _2262_keyType = _source98.dtor_keyType;
          DAST._IType _2263_valueType = _source98.dtor_valueType;
          unmatched98 = false;
          {
            RAST._IType _2264_kType;
            RAST._IType _out668;
            _out668 = (this).GenType(_2262_keyType, DCOMP.GenTypeContext.@default());
            _2264_kType = _out668;
            RAST._IType _2265_vType;
            RAST._IType _out669;
            _out669 = (this).GenType(_2263_valueType, DCOMP.GenTypeContext.@default());
            _2265_vType = _out669;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2264_kType, _2265_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out670;
            DCOMP._IOwnership _out671;
            (this).FromOwned(r, expectedOwnership, out _out670, out _out671);
            r = _out670;
            resultingOwnership = _out671;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_SetBuilder) {
          DAST._IType _2266_elemType = _source98.dtor_elemType;
          unmatched98 = false;
          {
            RAST._IType _2267_eType;
            RAST._IType _out672;
            _out672 = (this).GenType(_2266_elemType, DCOMP.GenTypeContext.@default());
            _2267_eType = _out672;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2267_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out673;
            DCOMP._IOwnership _out674;
            (this).FromOwned(r, expectedOwnership, out _out673, out _out674);
            r = _out673;
            resultingOwnership = _out674;
            return ;
          }
        }
      }
      if (unmatched98) {
        DAST._IType _2268_elemType = _source98.dtor_elemType;
        DAST._IExpression _2269_collection = _source98.dtor_collection;
        bool _2270_is__forall = _source98.dtor_is__forall;
        DAST._IExpression _2271_lambda = _source98.dtor_lambda;
        unmatched98 = false;
        {
          RAST._IType _2272_tpe;
          RAST._IType _out675;
          _out675 = (this).GenType(_2268_elemType, DCOMP.GenTypeContext.@default());
          _2272_tpe = _out675;
          RAST._IExpr _2273_collectionGen;
          DCOMP._IOwnership _2274___v230;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2275_recIdents;
          RAST._IExpr _out676;
          DCOMP._IOwnership _out677;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out678;
          (this).GenExpr(_2269_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out676, out _out677, out _out678);
          _2273_collectionGen = _out676;
          _2274___v230 = _out677;
          _2275_recIdents = _out678;
          Dafny.ISequence<DAST._IAttribute> _2276_extraAttributes;
          _2276_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2269_collection).is_IntRange) || ((_2269_collection).is_UnboundedIntRange)) || ((_2269_collection).is_SeqBoundedPool)) {
            _2276_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2271_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2277_formals;
            _2277_formals = (_2271_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2278_newFormals;
            _2278_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi54 = new BigInteger((_2277_formals).Count);
            for (BigInteger _2279_i = BigInteger.Zero; _2279_i < _hi54; _2279_i++) {
              var _pat_let_tv147 = _2276_extraAttributes;
              var _pat_let_tv148 = _2277_formals;
              _2278_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2278_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2277_formals).Select(_2279_i), _pat_let38_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let38_0, _2280_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv147, ((_pat_let_tv148).Select(_2279_i)).dtor_attributes), _pat_let39_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let39_0, _2281_dt__update_hattributes_h0 => DAST.Formal.create((_2280_dt__update__tmp_h0).dtor_name, (_2280_dt__update__tmp_h0).dtor_typ, _2281_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv149 = _2278_newFormals;
            DAST._IExpression _2282_newLambda;
            _2282_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2271_lambda, _pat_let40_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let40_0, _2283_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv149, _pat_let41_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let41_0, _2284_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2284_dt__update_hparams_h0, (_2283_dt__update__tmp_h1).dtor_retType, (_2283_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2285_lambdaGen;
            DCOMP._IOwnership _2286___v231;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2287_recLambdaIdents;
            RAST._IExpr _out679;
            DCOMP._IOwnership _out680;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out681;
            (this).GenExpr(_2282_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out679, out _out680, out _out681);
            _2285_lambdaGen = _out679;
            _2286___v231 = _out680;
            _2287_recLambdaIdents = _out681;
            Dafny.ISequence<Dafny.Rune> _2288_fn;
            _2288_fn = ((_2270_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2273_collectionGen).Sel(_2288_fn)).Apply1(((_2285_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2275_recIdents, _2287_recLambdaIdents);
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Quantifier without an inline lambda"));
            r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
          RAST._IExpr _out682;
          DCOMP._IOwnership _out683;
          (this).FromOwned(r, expectedOwnership, out _out682, out _out683);
          r = _out682;
          resultingOwnership = _out683;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> externalFiles)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      Dafny.ISequence<RAST._IModDecl> _2289_externUseDecls;
      _2289_externUseDecls = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi55 = new BigInteger((externalFiles).Count);
      for (BigInteger _2290_i = BigInteger.Zero; _2290_i < _hi55; _2290_i++) {
        Dafny.ISequence<Dafny.Rune> _2291_externalFile;
        _2291_externalFile = (externalFiles).Select(_2290_i);
        Dafny.ISequence<Dafny.Rune> _2292_externalMod;
        _2292_externalMod = _2291_externalFile;
        if (((new BigInteger((_2291_externalFile).Count)) > (new BigInteger(3))) && (((_2291_externalFile).Drop((new BigInteger((_2291_externalFile).Count)) - (new BigInteger(3)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".rs")))) {
          _2292_externalMod = (_2291_externalFile).Subsequence(BigInteger.Zero, (new BigInteger((_2291_externalFile).Count)) - (new BigInteger(3)));
        } else {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unrecognized external file "), _2291_externalFile), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". External file must be *.rs files")));
        }
        RAST._IMod _2293_externMod;
        _2293_externMod = RAST.Mod.create_ExternMod(_2292_externalMod);
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (_2293_externMod)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        _2289_externUseDecls = Dafny.Sequence<RAST._IModDecl>.Concat(_2289_externUseDecls, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), ((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"))).MSel(_2292_externalMod)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))));
      }
      if (!(_2289_externUseDecls).Equals(Dafny.Sequence<RAST._IModDecl>.FromElements())) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (RAST.Mod.create_Mod(DCOMP.COMP.DAFNY__EXTERN__MODULE, _2289_externUseDecls))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
      }
      BigInteger _hi56 = new BigInteger((p).Count);
      for (BigInteger _2294_i = BigInteger.Zero; _2294_i < _hi56; _2294_i++) {
        RAST._IMod _2295_m;
        RAST._IMod _out684;
        _out684 = (this).GenModule((p).Select(_2294_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2295_m = _out684;
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (_2295_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2296_i;
      _2296_i = BigInteger.Zero;
      while ((_2296_i) < (new BigInteger((fullName).Count))) {
        if ((_2296_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2296_i)));
        _2296_i = (_2296_i) + (BigInteger.One);
      }
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("();\n}"));
      return s;
    }
    public bool _UnicodeChars {get; set;}
    public bool UnicodeChars { get {
      return this._UnicodeChars;
    } }
    public Dafny.ISequence<Dafny.Rune> DafnyChar { get {
      if ((this).UnicodeChars) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyChar");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyCharUTF16");
      }
    } }
    public RAST._IType DafnyCharUnderlying { get {
      if ((this).UnicodeChars) {
        return RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"));
      } else {
        return RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u16"));
      }
    } }
    public Dafny.ISequence<Dafny.Rune> string__of { get {
      if ((this).UnicodeChars) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("string_of");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("string_utf16_of");
      }
    } }
    public DCOMP._IObjectType _ObjectType {get; set;}
    public DCOMP._IObjectType ObjectType { get {
      return this._ObjectType;
    } }
    public Dafny.ISequence<Dafny.Rune> allocate { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("allocate");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("allocate_object");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> allocate__fn { get {
      return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), (this).allocate);
    } }
    public Dafny.ISequence<Dafny.Rune> update__field__uninit__macro { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_uninit!");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_uninit_object!");
      }
    } }
    public RAST._IExpr thisInConstructor { get {
      if (((this).ObjectType).is_RawPointers) {
        return RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
      } else {
        return (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))).Clone();
      }
    } }
    public Dafny.ISequence<Dafny.Rune> array__construct { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("construct");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("construct_object");
      }
    } }
    public RAST._IExpr modify__macro { get {
      return (RAST.__default.dafny__runtime).MSel(((((this).ObjectType).is_RawPointers) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("modify!")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("md!"))));
    } }
    public RAST._IExpr read__macro { get {
      return (RAST.__default.dafny__runtime).MSel(((((this).ObjectType).is_RawPointers) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read!")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rd!"))));
    } }
    public Dafny.ISequence<Dafny.Rune> placebos__usize { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("placebos_usize");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("placebos_usize_object");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> update__field__if__uninit__macro { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_if_uninit!");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_field_if_uninit_object!");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> Upcast { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Upcast");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("UpcastObject");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> UpcastFnMacro { get {
      return Dafny.Sequence<Dafny.Rune>.Concat((this).Upcast, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Fn!"));
    } }
    public Dafny.ISequence<Dafny.Rune> upcast { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_object");
      }
    } }
    public Dafny.ISequence<Dafny.Rune> downcast { get {
      if (((this).ObjectType).is_RawPointers) {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cast!");
      } else {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cast_object!");
      }
    } }
    public static Dafny.IMap<DAST._IBinOp,Dafny.ISequence<Dafny.Rune>> OpTable { get {
      return Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Mod(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_And(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Or(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Div(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Lt(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_LtChar(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Plus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Minus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Times(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseAnd(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseOr(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseXor(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftRight(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftLeft(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<")));
    } }
    public static Dafny.ISequence<Dafny.Rune> DAFNY__EXTERN__MODULE { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_dafny_externs");
    } }
  }
} // end of namespace DCOMP