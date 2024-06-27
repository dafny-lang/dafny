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
            Dafny.ISequence<Dafny.Rune> _in121 = (i).Drop(new BigInteger(2));
            i = _in121;
            goto TAIL_CALL_START;
          }
        } else {
          return true;
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _in122 = (i).Drop(BigInteger.One);
        i = _in122;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> idiomatic__rust(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1128___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1128___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1128___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1128___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in123 = (i).Drop(new BigInteger(2));
        i = _in123;
        goto TAIL_CALL_START;
      } else {
        _1128___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1128___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(BigInteger.One);
        i = _in124;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1129___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1129___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1129___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1129___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      } else {
        _1129___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1129___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in126 = (i).Drop(BigInteger.One);
        i = _in126;
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
        Dafny.ISequence<Dafny.Rune> _1130_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1130_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeField(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1131_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1131_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1131_r);
      } else {
        return DCOMP.__default.escapeName(f);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeDtor(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1132_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1132_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1132_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": r#_")), _1132_r);
      } else {
        return DCOMP.__default.escapeName(f);
      }
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
      var _pat_let_tv136 = dafnyName;
      var _pat_let_tv137 = rs;
      var _pat_let_tv138 = dafnyName;
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _1133_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source53 = (rs).Select(BigInteger.Zero);
          bool unmatched53 = true;
          if (unmatched53) {
            if (_source53.is_UserDefined) {
              DAST._IResolvedType _1134_resolvedType = _source53.dtor_resolved;
              unmatched53 = false;
              return DCOMP.__default.TraitTypeContainingMethod(_1134_resolvedType, _pat_let_tv136);
            }
          }
          if (unmatched53) {
            unmatched53 = false;
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
          throw new System.Exception("unexpected control point");
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source54 = _1133_res;
        bool unmatched54 = true;
        if (unmatched54) {
          if (_source54.is_Some) {
            unmatched54 = false;
            return _1133_res;
          }
        }
        if (unmatched54) {
          unmatched54 = false;
          return DCOMP.__default.TraitTypeContainingMethodAux((_pat_let_tv137).Drop(BigInteger.One), _pat_let_tv138);
        }
        throw new System.Exception("unexpected control point");
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethod(DAST._IResolvedType r, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DAST._IResolvedType _let_tmp_rhs53 = r;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1135_path = _let_tmp_rhs53.dtor_path;
      Dafny.ISequence<DAST._IType> _1136_typeArgs = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedTypeBase _1137_kind = _let_tmp_rhs53.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1138_attributes = _let_tmp_rhs53.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1139_properMethods = _let_tmp_rhs53.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1140_extendedTypes = _let_tmp_rhs53.dtor_extendedTypes;
      if ((_1139_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1140_extendedTypes, dafnyName);
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
      Dafny.ISequence<Dafny.Rune> _1141___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1141___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((s).Select(BigInteger.Zero)) == (new Dafny.Rune(' '))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1141___accumulator, s);
      } else {
        _1141___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1141___accumulator, ((((s).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")) : (Dafny.Sequence<Dafny.Rune>.FromElements((s).Select(BigInteger.Zero)))));
        Dafny.ISequence<Dafny.Rune> _in127 = (s).Drop(BigInteger.One);
        s = _in127;
        goto TAIL_CALL_START;
      }
    }
    public static DCOMP._IExternAttribute ExtractExtern(Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DCOMP._IExternAttribute res = DCOMP.ExternAttribute.Default();
      BigInteger _hi5 = new BigInteger((attributes).Count);
      for (BigInteger _1142_i = BigInteger.Zero; _1142_i < _hi5; _1142_i++) {
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _1143_attr;
        _1143_attr = DCOMP.__default.OptExtern((attributes).Select(_1142_i), dafnyName);
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _source55 = _1143_attr;
        bool unmatched55 = true;
        if (unmatched55) {
          if (_source55.is_Some) {
            DCOMP._IExternAttribute _1144_n = _source55.dtor_value;
            unmatched55 = false;
            res = _1144_n;
            return res;
          }
        }
        if (unmatched55) {
          unmatched55 = false;
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
      DCOMP._IEnvironment _1145_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1146_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll6 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1147_k = (Dafny.ISequence<Dafny.Rune>)_compr_6;
          if (((this).dtor_types).Contains(_1147_k)) {
            _coll6.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_1147_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_1147_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll6);
      }))();
      return DCOMP.Environment.create((_1145_dt__update__tmp_h0).dtor_names, _1146_dt__update_htypes_h0);
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
      BigInteger _1148_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1148_indexInEnv), ((this).dtor_names).Drop((_1148_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _1149_modName;
      _1149_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1149_modName);
      } else {
        DCOMP._IExternAttribute _1150_optExtern;
        _1150_optExtern = DCOMP.__default.ExtractExternMod(mod);
        Dafny.ISequence<RAST._IModDecl> _1151_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1151_body = _out15;
        if ((_1150_optExtern).is_SimpleExtern) {
          if ((mod).dtor_requiresExterns) {
            _1151_body = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"))).MSel(DCOMP.COMP.DAFNY__EXTERN__MODULE)).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1150_optExtern).dtor_overrideName))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))), _1151_body);
          }
        } else if ((_1150_optExtern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Externs on modules can only have 1 string argument"));
        } else if ((_1150_optExtern).is_UnsupportedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some((_1150_optExtern).dtor_reason);
        }
        s = RAST.Mod.create_Mod(_1149_modName, _1151_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi6 = new BigInteger((body).Count);
      for (BigInteger _1152_i = BigInteger.Zero; _1152_i < _hi6; _1152_i++) {
        Dafny.ISequence<RAST._IModDecl> _1153_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source56 = (body).Select(_1152_i);
        bool unmatched56 = true;
        if (unmatched56) {
          if (_source56.is_Module) {
            DAST._IModule _1154_m = _source56.dtor_Module_a0;
            unmatched56 = false;
            RAST._IMod _1155_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1154_m, containingPath);
            _1155_mm = _out16;
            _1153_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1155_mm));
          }
        }
        if (unmatched56) {
          if (_source56.is_Class) {
            DAST._IClass _1156_c = _source56.dtor_Class_a0;
            unmatched56 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1156_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1156_c).dtor_name)));
            _1153_generated = _out17;
          }
        }
        if (unmatched56) {
          if (_source56.is_Trait) {
            DAST._ITrait _1157_t = _source56.dtor_Trait_a0;
            unmatched56 = false;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenTrait(_1157_t, containingPath);
            _1153_generated = _out18;
          }
        }
        if (unmatched56) {
          if (_source56.is_Newtype) {
            DAST._INewtype _1158_n = _source56.dtor_Newtype_a0;
            unmatched56 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1158_n);
            _1153_generated = _out19;
          }
        }
        if (unmatched56) {
          if (_source56.is_SynonymType) {
            DAST._ISynonymType _1159_s = _source56.dtor_SynonymType_a0;
            unmatched56 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1159_s);
            _1153_generated = _out20;
          }
        }
        if (unmatched56) {
          DAST._IDatatype _1160_d = _source56.dtor_Datatype_a0;
          unmatched56 = false;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1160_d);
          _1153_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1153_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1161_genTpConstraint;
      _1161_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1161_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1161_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1161_genTpConstraint);
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
        for (BigInteger _1162_tpI = BigInteger.Zero; _1162_tpI < _hi7; _1162_tpI++) {
          DAST._ITypeArgDecl _1163_tp;
          _1163_tp = (@params).Select(_1162_tpI);
          DAST._IType _1164_typeArg;
          RAST._ITypeParamDecl _1165_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1163_tp, out _out22, out _out23);
          _1164_typeArg = _out22;
          _1165_typeParam = _out23;
          RAST._IType _1166_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1164_typeArg, DCOMP.GenTypeContext.@default());
          _1166_rType = _out24;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1164_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1166_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1165_typeParam));
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
      Dafny.ISequence<DAST._IType> _1167_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1168_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1169_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1170_whereConstraints;
      Dafny.ISequence<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1167_typeParamsSeq = _out25;
      _1168_rTypeParams = _out26;
      _1169_rTypeParamsDecls = _out27;
      _1170_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1171_constrainedTypeParams;
      _1171_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1169_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1172_fields;
      _1172_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1173_fieldInits;
      _1173_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi8 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1174_fieldI = BigInteger.Zero; _1174_fieldI < _hi8; _1174_fieldI++) {
        DAST._IField _1175_field;
        _1175_field = ((c).dtor_fields).Select(_1174_fieldI);
        RAST._IType _1176_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1175_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1176_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1177_fieldRustName;
        _1177_fieldRustName = DCOMP.__default.escapeName(((_1175_field).dtor_formal).dtor_name);
        _1172_fields = Dafny.Sequence<RAST._IField>.Concat(_1172_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1177_fieldRustName, _1176_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source57 = (_1175_field).dtor_defaultValue;
        bool unmatched57 = true;
        if (unmatched57) {
          if (_source57.is_Some) {
            DAST._IExpression _1178_e = _source57.dtor_value;
            unmatched57 = false;
            {
              RAST._IExpr _1179_expr;
              DCOMP._IOwnership _1180___v49;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1181___v50;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1178_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1179_expr = _out30;
              _1180___v49 = _out31;
              _1181___v50 = _out32;
              _1173_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1173_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1177_fieldRustName, _1179_expr)));
            }
          }
        }
        if (unmatched57) {
          unmatched57 = false;
          {
            RAST._IExpr _1182_default;
            _1182_default = RAST.__default.std__Default__default;
            if ((_1176_fieldType).IsObjectOrPointer()) {
              _1182_default = (_1176_fieldType).ToNullExpr();
            }
            _1173_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1173_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1177_fieldRustName, _1182_default)));
          }
        }
      }
      BigInteger _hi9 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1183_typeParamI = BigInteger.Zero; _1183_typeParamI < _hi9; _1183_typeParamI++) {
        DAST._IType _1184_typeArg;
        RAST._ITypeParamDecl _1185_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1183_typeParamI), out _out33, out _out34);
        _1184_typeArg = _out33;
        _1185_typeParam = _out34;
        RAST._IType _1186_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1184_typeArg, DCOMP.GenTypeContext.@default());
        _1186_rTypeArg = _out35;
        _1172_fields = Dafny.Sequence<RAST._IField>.Concat(_1172_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1183_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1186_rTypeArg))))));
        _1173_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1173_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1183_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      DCOMP._IExternAttribute _1187_extern;
      _1187_extern = DCOMP.__default.ExtractExtern((c).dtor_attributes, (c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _1188_className = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((_1187_extern).is_SimpleExtern) {
        _1188_className = (_1187_extern).dtor_overrideName;
      } else {
        _1188_className = DCOMP.__default.escapeName((c).dtor_name);
        if ((_1187_extern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multi-argument externs not supported for classes yet"));
        }
      }
      RAST._IStruct _1189_struct;
      _1189_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1188_className, _1169_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1172_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_1187_extern).is_NoExtern) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1189_struct)));
      }
      Dafny.ISequence<RAST._IImplMember> _1190_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1191_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1167_typeParamsSeq, out _out36, out _out37);
      _1190_implBody = _out36;
      _1191_traitBodies = _out37;
      if ((_1187_extern).is_NoExtern) {
        _1190_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.Type.create_SelfOwned())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel((this).allocate)).ApplyType1(RAST.Type.create_SelfOwned())).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1190_implBody);
      }
      RAST._IType _1192_selfTypeForImpl = RAST.Type.Default();
      if (((_1187_extern).is_NoExtern) || ((_1187_extern).is_UnsupportedExtern)) {
        _1192_selfTypeForImpl = RAST.Type.create_TIdentifier(_1188_className);
      } else if ((_1187_extern).is_AdvancedExtern) {
        _1192_selfTypeForImpl = ((RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"))).MSel((_1187_extern).dtor_enclosingModule)).MSel((_1187_extern).dtor_overrideName);
      } else if ((_1187_extern).is_SimpleExtern) {
        _1192_selfTypeForImpl = RAST.Type.create_TIdentifier((_1187_extern).dtor_overrideName);
      }
      if ((new BigInteger((_1190_implBody).Count)).Sign == 1) {
        RAST._IImpl _1193_i;
        _1193_i = RAST.Impl.create_Impl(_1169_rTypeParamsDecls, RAST.Type.create_TypeApp(_1192_selfTypeForImpl, _1168_rTypeParams), _1170_whereConstraints, _1190_implBody);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1193_i)));
      }
      RAST._IType _1194_genSelfPath;
      RAST._IType _out38;
      _out38 = DCOMP.COMP.GenPath(path);
      _1194_genSelfPath = _out38;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1169_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"))))), RAST.Type.create_TypeApp(_1194_genSelfPath, _1168_rTypeParams), _1170_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any")))))))))));
      Dafny.ISequence<DAST._IType> _1195_superClasses;
      _1195_superClasses = (((_1188_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) ? (Dafny.Sequence<DAST._IType>.FromElements()) : ((c).dtor_superClasses));
      BigInteger _hi10 = new BigInteger((_1195_superClasses).Count);
      for (BigInteger _1196_i = BigInteger.Zero; _1196_i < _hi10; _1196_i++) {
        DAST._IType _1197_superClass;
        _1197_superClass = (_1195_superClasses).Select(_1196_i);
        DAST._IType _source58 = _1197_superClass;
        bool unmatched58 = true;
        if (unmatched58) {
          if (_source58.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source58.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1198_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1199_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1200_properMethods = resolved0.dtor_properMethods;
              unmatched58 = false;
              {
                RAST._IType _1201_pathStr;
                RAST._IType _out39;
                _out39 = DCOMP.COMP.GenPath(_1198_traitPath);
                _1201_pathStr = _out39;
                Dafny.ISequence<RAST._IType> _1202_typeArgs;
                Dafny.ISequence<RAST._IType> _out40;
                _out40 = (this).GenTypeArgs(_1199_typeArgs, DCOMP.GenTypeContext.@default());
                _1202_typeArgs = _out40;
                Dafny.ISequence<RAST._IImplMember> _1203_body;
                _1203_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1191_traitBodies).Contains(_1198_traitPath)) {
                  _1203_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1191_traitBodies,_1198_traitPath);
                }
                RAST._IType _1204_traitType;
                _1204_traitType = RAST.Type.create_TypeApp(_1201_pathStr, _1202_typeArgs);
                if (!((_1187_extern).is_NoExtern)) {
                  if (((new BigInteger((_1203_body).Count)).Sign == 0) && ((new BigInteger((_1200_properMethods).Count)).Sign != 0)) {
                    goto continue_0;
                  }
                  if ((new BigInteger((_1203_body).Count)) != (new BigInteger((_1200_properMethods).Count))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: In the class "), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(path, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1205_s) => {
  return ((_1205_s));
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", some proper methods of ")), (_1204_traitType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" are marked {:extern} and some are not.")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" For the Rust compiler, please make all methods (")), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_1200_properMethods, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1206_s) => {
  return ((_1206_s));
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")  bodiless and mark as {:extern} and implement them in a Rust file, ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("or mark none of them as {:extern} and implement them in Dafny. ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.")));
                  }
                }
                RAST._IModDecl _1207_x;
                _1207_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1169_rTypeParamsDecls, _1204_traitType, RAST.Type.create_TypeApp(_1194_genSelfPath, _1168_rTypeParams), _1170_whereConstraints, _1203_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1207_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1169_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1204_traitType))), RAST.Type.create_TypeApp(_1194_genSelfPath, _1168_rTypeParams), _1170_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1204_traitType)))))))));
              }
            }
          }
        }
        if (unmatched58) {
          unmatched58 = false;
        }
      continue_0: ;
      }
    after_0: ;
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1208_typeParamsSeq;
      _1208_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1209_typeParamDecls;
      _1209_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1210_typeParams;
      _1210_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi11 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1211_tpI = BigInteger.Zero; _1211_tpI < _hi11; _1211_tpI++) {
          DAST._ITypeArgDecl _1212_tp;
          _1212_tp = ((t).dtor_typeParams).Select(_1211_tpI);
          DAST._IType _1213_typeArg;
          RAST._ITypeParamDecl _1214_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1212_tp, out _out41, out _out42);
          _1213_typeArg = _out41;
          _1214_typeParamDecl = _out42;
          _1208_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1208_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1213_typeArg));
          _1209_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1209_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1214_typeParamDecl));
          RAST._IType _1215_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1213_typeArg, DCOMP.GenTypeContext.@default());
          _1215_typeParam = _out43;
          _1210_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1210_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1215_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1216_fullPath;
      _1216_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1217_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1218___v54;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1216_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1208_typeParamsSeq, out _out44, out _out45);
      _1217_implBody = _out44;
      _1218___v54 = _out45;
      Dafny.ISequence<RAST._IType> _1219_parents;
      _1219_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi12 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1220_i = BigInteger.Zero; _1220_i < _hi12; _1220_i++) {
        RAST._IType _1221_tpe;
        RAST._IType _out46;
        _out46 = (this).GenType(((t).dtor_parents).Select(_1220_i), DCOMP.GenTypeContext.ForTraitParents());
        _1221_tpe = _out46;
        _1219_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1219_parents, Dafny.Sequence<RAST._IType>.FromElements(_1221_tpe)), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply1(RAST.Type.create_DynType(_1221_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1209_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1210_typeParams), _1219_parents, _1217_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1222_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1223_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1224_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1225_whereConstraints;
      Dafny.ISequence<DAST._IType> _out47;
      Dafny.ISequence<RAST._IType> _out48;
      Dafny.ISequence<RAST._ITypeParamDecl> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1222_typeParamsSeq = _out47;
      _1223_rTypeParams = _out48;
      _1224_rTypeParamsDecls = _out49;
      _1225_whereConstraints = _out50;
      Dafny.ISequence<Dafny.Rune> _1226_constrainedTypeParams;
      _1226_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1224_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1227_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source59 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched59 = true;
      if (unmatched59) {
        if (_source59.is_Some) {
          RAST._IType _1228_v = _source59.dtor_value;
          unmatched59 = false;
          _1227_underlyingType = _1228_v;
        }
      }
      if (unmatched59) {
        unmatched59 = false;
        RAST._IType _out51;
        _out51 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1227_underlyingType = _out51;
      }
      DAST._IType _1229_resultingType;
      _1229_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1230_newtypeName;
      _1230_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1230_newtypeName, _1224_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1227_underlyingType))))));
      RAST._IExpr _1231_fnBody;
      _1231_fnBody = RAST.Expr.create_Identifier(_1230_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source60 = (c).dtor_witnessExpr;
      bool unmatched60 = true;
      if (unmatched60) {
        if (_source60.is_Some) {
          DAST._IExpression _1232_e = _source60.dtor_value;
          unmatched60 = false;
          {
            DAST._IExpression _1233_e;
            _1233_e = ((object.Equals((c).dtor_base, _1229_resultingType)) ? (_1232_e) : (DAST.Expression.create_Convert(_1232_e, (c).dtor_base, _1229_resultingType)));
            RAST._IExpr _1234_eStr;
            DCOMP._IOwnership _1235___v55;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1236___v56;
            RAST._IExpr _out52;
            DCOMP._IOwnership _out53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out54;
            (this).GenExpr(_1233_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out52, out _out53, out _out54);
            _1234_eStr = _out52;
            _1235___v55 = _out53;
            _1236___v56 = _out54;
            _1231_fnBody = (_1231_fnBody).Apply1(_1234_eStr);
          }
        }
      }
      if (unmatched60) {
        unmatched60 = false;
        {
          _1231_fnBody = (_1231_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1237_body;
      _1237_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1231_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source61 = (c).dtor_constraint;
      bool unmatched61 = true;
      if (unmatched61) {
        if (_source61.is_None) {
          unmatched61 = false;
        }
      }
      if (unmatched61) {
        DAST._INewtypeConstraint value8 = _source61.dtor_value;
        DAST._IFormal _1238_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1239_constraintStmts = value8.dtor_constraintStmts;
        unmatched61 = false;
        RAST._IExpr _1240_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1241___v57;
        DCOMP._IEnvironment _1242_newEnv;
        RAST._IExpr _out55;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out56;
        DCOMP._IEnvironment _out57;
        (this).GenStmts(_1239_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out55, out _out56, out _out57);
        _1240_rStmts = _out55;
        _1241___v57 = _out56;
        _1242_newEnv = _out57;
        Dafny.ISequence<RAST._IFormal> _1243_rFormals;
        Dafny.ISequence<RAST._IFormal> _out58;
        _out58 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1238_formal));
        _1243_rFormals = _out58;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1224_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1230_newtypeName), _1223_rTypeParams), _1225_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1243_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1240_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1224_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1230_newtypeName), _1223_rTypeParams), _1225_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1237_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1224_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1230_newtypeName), _1223_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1224_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1230_newtypeName), _1223_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1227_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1244_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1245_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1246_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1247_whereConstraints;
      Dafny.ISequence<DAST._IType> _out59;
      Dafny.ISequence<RAST._IType> _out60;
      Dafny.ISequence<RAST._ITypeParamDecl> _out61;
      Dafny.ISequence<Dafny.Rune> _out62;
      (this).GenTypeParameters((c).dtor_typeParams, out _out59, out _out60, out _out61, out _out62);
      _1244_typeParamsSeq = _out59;
      _1245_rTypeParams = _out60;
      _1246_rTypeParamsDecls = _out61;
      _1247_whereConstraints = _out62;
      Dafny.ISequence<Dafny.Rune> _1248_constrainedTypeParams;
      _1248_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1246_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _1249_synonymTypeName;
      _1249_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1250_resultingType;
      RAST._IType _out63;
      _out63 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1250_resultingType = _out63;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1249_synonymTypeName, _1246_rTypeParamsDecls, _1250_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source62 = (c).dtor_witnessExpr;
      bool unmatched62 = true;
      if (unmatched62) {
        if (_source62.is_Some) {
          DAST._IExpression _1251_e = _source62.dtor_value;
          unmatched62 = false;
          {
            RAST._IExpr _1252_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1253___v58;
            DCOMP._IEnvironment _1254_newEnv;
            RAST._IExpr _out64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out65;
            DCOMP._IEnvironment _out66;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out64, out _out65, out _out66);
            _1252_rStmts = _out64;
            _1253___v58 = _out65;
            _1254_newEnv = _out66;
            RAST._IExpr _1255_rExpr;
            DCOMP._IOwnership _1256___v59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1257___v60;
            RAST._IExpr _out67;
            DCOMP._IOwnership _out68;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out69;
            (this).GenExpr(_1251_e, DCOMP.SelfInfo.create_NoSelf(), _1254_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out67, out _out68, out _out69);
            _1255_rExpr = _out67;
            _1256___v59 = _out68;
            _1257___v60 = _out69;
            Dafny.ISequence<Dafny.Rune> _1258_constantName;
            _1258_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1258_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1250_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1252_rStmts).Then(_1255_rExpr)))))));
          }
        }
      }
      if (unmatched62) {
        unmatched62 = false;
      }
      return s;
    }
    public bool TypeIsEq(DAST._IType t) {
      DAST._IType _source63 = t;
      bool unmatched63 = true;
      if (unmatched63) {
        if (_source63.is_UserDefined) {
          unmatched63 = false;
          return true;
        }
      }
      if (unmatched63) {
        if (_source63.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1259_ts = _source63.dtor_Tuple_a0;
          unmatched63 = false;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1260_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1260_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1261_t = (DAST._IType)_forall_var_5;
            return !((_1260_ts).Contains(_1261_t)) || ((this).TypeIsEq(_1261_t));
          }))))(_1259_ts);
        }
      }
      if (unmatched63) {
        if (_source63.is_Array) {
          DAST._IType _1262_t = _source63.dtor_element;
          unmatched63 = false;
          return (this).TypeIsEq(_1262_t);
        }
      }
      if (unmatched63) {
        if (_source63.is_Seq) {
          DAST._IType _1263_t = _source63.dtor_element;
          unmatched63 = false;
          return (this).TypeIsEq(_1263_t);
        }
      }
      if (unmatched63) {
        if (_source63.is_Set) {
          DAST._IType _1264_t = _source63.dtor_element;
          unmatched63 = false;
          return (this).TypeIsEq(_1264_t);
        }
      }
      if (unmatched63) {
        if (_source63.is_Multiset) {
          DAST._IType _1265_t = _source63.dtor_element;
          unmatched63 = false;
          return (this).TypeIsEq(_1265_t);
        }
      }
      if (unmatched63) {
        if (_source63.is_Map) {
          DAST._IType _1266_k = _source63.dtor_key;
          DAST._IType _1267_v = _source63.dtor_value;
          unmatched63 = false;
          return ((this).TypeIsEq(_1266_k)) && ((this).TypeIsEq(_1267_v));
        }
      }
      if (unmatched63) {
        if (_source63.is_SetBuilder) {
          DAST._IType _1268_t = _source63.dtor_element;
          unmatched63 = false;
          return (this).TypeIsEq(_1268_t);
        }
      }
      if (unmatched63) {
        if (_source63.is_MapBuilder) {
          DAST._IType _1269_k = _source63.dtor_key;
          DAST._IType _1270_v = _source63.dtor_value;
          unmatched63 = false;
          return ((this).TypeIsEq(_1269_k)) && ((this).TypeIsEq(_1270_v));
        }
      }
      if (unmatched63) {
        if (_source63.is_Arrow) {
          unmatched63 = false;
          return false;
        }
      }
      if (unmatched63) {
        if (_source63.is_Primitive) {
          unmatched63 = false;
          return true;
        }
      }
      if (unmatched63) {
        if (_source63.is_Passthrough) {
          unmatched63 = false;
          return true;
        }
      }
      if (unmatched63) {
        if (_source63.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _1271_i = _source63.dtor_TypeArg_a0;
          unmatched63 = false;
          return true;
        }
      }
      if (unmatched63) {
        unmatched63 = false;
        return true;
      }
      throw new System.Exception("unexpected control point");
    }
    public bool DatatypeIsEq(DAST._IDatatype c) {
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1272_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1272_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1273_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1273_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1274_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1272_c).dtor_ctors).Contains(_1273_ctor)) && (((_1273_ctor).dtor_args).Contains(_1274_arg))) || ((this).TypeIsEq(((_1274_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1275_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1276_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1277_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1278_whereConstraints;
      Dafny.ISequence<DAST._IType> _out70;
      Dafny.ISequence<RAST._IType> _out71;
      Dafny.ISequence<RAST._ITypeParamDecl> _out72;
      Dafny.ISequence<Dafny.Rune> _out73;
      (this).GenTypeParameters((c).dtor_typeParams, out _out70, out _out71, out _out72, out _out73);
      _1275_typeParamsSeq = _out70;
      _1276_rTypeParams = _out71;
      _1277_rTypeParamsDecls = _out72;
      _1278_whereConstraints = _out73;
      Dafny.ISequence<Dafny.Rune> _1279_datatypeName;
      _1279_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1280_ctors;
      _1280_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _1281_variances;
      _1281_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_1282_typeParamDecl) => {
        return (_1282_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1283_i = BigInteger.Zero; _1283_i < _hi13; _1283_i++) {
        DAST._IDatatypeCtor _1284_ctor;
        _1284_ctor = ((c).dtor_ctors).Select(_1283_i);
        Dafny.ISequence<RAST._IField> _1285_ctorArgs;
        _1285_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1286_isNumeric;
        _1286_isNumeric = false;
        BigInteger _hi14 = new BigInteger(((_1284_ctor).dtor_args).Count);
        for (BigInteger _1287_j = BigInteger.Zero; _1287_j < _hi14; _1287_j++) {
          DAST._IDatatypeDtor _1288_dtor;
          _1288_dtor = ((_1284_ctor).dtor_args).Select(_1287_j);
          RAST._IType _1289_formalType;
          RAST._IType _out74;
          _out74 = (this).GenType(((_1288_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1289_formalType = _out74;
          Dafny.ISequence<Dafny.Rune> _1290_formalName;
          _1290_formalName = DCOMP.__default.escapeName(((_1288_dtor).dtor_formal).dtor_name);
          if (((_1287_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1290_formalName))) {
            _1286_isNumeric = true;
          }
          if ((((_1287_j).Sign != 0) && (_1286_isNumeric)) && (!(Std.Strings.__default.OfNat(_1287_j)).Equals(_1290_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1290_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1287_j)));
            _1286_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1285_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1285_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1290_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1289_formalType))))));
          } else {
            _1285_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1285_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1290_formalName, _1289_formalType))));
          }
        }
        RAST._IFields _1291_namedFields;
        _1291_namedFields = RAST.Fields.create_NamedFields(_1285_ctorArgs);
        if (_1286_isNumeric) {
          _1291_namedFields = (_1291_namedFields).ToNamelessFields();
        }
        _1280_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1280_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1284_ctor).dtor_name), _1291_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1292_selfPath;
      _1292_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1293_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1294_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out75;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out76;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1292_selfPath, _1275_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1281_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1275_typeParamsSeq, out _out75, out _out76);
      _1293_implBodyRaw = _out75;
      _1294_traitBodies = _out76;
      Dafny.ISequence<RAST._IImplMember> _1295_implBody;
      _1295_implBody = _1293_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1296_emittedFields;
      _1296_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi15 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1297_i = BigInteger.Zero; _1297_i < _hi15; _1297_i++) {
        DAST._IDatatypeCtor _1298_ctor;
        _1298_ctor = ((c).dtor_ctors).Select(_1297_i);
        BigInteger _hi16 = new BigInteger(((_1298_ctor).dtor_args).Count);
        for (BigInteger _1299_j = BigInteger.Zero; _1299_j < _hi16; _1299_j++) {
          DAST._IDatatypeDtor _1300_dtor;
          _1300_dtor = ((_1298_ctor).dtor_args).Select(_1299_j);
          Dafny.ISequence<Dafny.Rune> _1301_callName;
          _1301_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1300_dtor).dtor_callName, DCOMP.__default.escapeName(((_1300_dtor).dtor_formal).dtor_name));
          if (!((_1296_emittedFields).Contains(_1301_callName))) {
            _1296_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1296_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1301_callName));
            RAST._IType _1302_formalType;
            RAST._IType _out77;
            _out77 = (this).GenType(((_1300_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1302_formalType = _out77;
            Dafny.ISequence<RAST._IMatchCase> _1303_cases;
            _1303_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi17 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1304_k = BigInteger.Zero; _1304_k < _hi17; _1304_k++) {
              DAST._IDatatypeCtor _1305_ctor2;
              _1305_ctor2 = ((c).dtor_ctors).Select(_1304_k);
              Dafny.ISequence<Dafny.Rune> _1306_pattern;
              _1306_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1279_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1305_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1307_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1308_hasMatchingField;
              _1308_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1309_patternInner;
              _1309_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1310_isNumeric;
              _1310_isNumeric = false;
              BigInteger _hi18 = new BigInteger(((_1305_ctor2).dtor_args).Count);
              for (BigInteger _1311_l = BigInteger.Zero; _1311_l < _hi18; _1311_l++) {
                DAST._IDatatypeDtor _1312_dtor2;
                _1312_dtor2 = ((_1305_ctor2).dtor_args).Select(_1311_l);
                Dafny.ISequence<Dafny.Rune> _1313_patternName;
                _1313_patternName = DCOMP.__default.escapeDtor(((_1312_dtor2).dtor_formal).dtor_name);
                if (((_1311_l).Sign == 0) && ((_1313_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1310_isNumeric = true;
                }
                if (_1310_isNumeric) {
                  _1313_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1312_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1311_l)));
                }
                if (object.Equals(((_1300_dtor).dtor_formal).dtor_name, ((_1312_dtor2).dtor_formal).dtor_name)) {
                  _1308_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(DCOMP.__default.escapeField(((_1312_dtor2).dtor_formal).dtor_name));
                }
                _1309_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1309_patternInner, _1313_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1310_isNumeric) {
                _1306_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1306_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1309_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1306_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1306_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1309_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1308_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1307_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1308_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1307_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1308_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1307_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _1314_ctorMatch;
              _1314_ctorMatch = RAST.MatchCase.create(_1306_pattern, RAST.Expr.create_RawExpr(_1307_rhs));
              _1303_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1303_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1314_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1303_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1303_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1279_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _1315_methodBody;
            _1315_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1303_cases);
            _1295_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1295_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1301_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1302_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1315_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1316_coerceTypes;
      _1316_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1317_rCoerceTypeParams;
      _1317_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1318_coerceArguments;
      _1318_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1319_coerceMap;
      _1319_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1320_rCoerceMap;
      _1320_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1321_coerceMapToArg;
      _1321_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1322_types;
        _1322_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi19 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1323_typeI = BigInteger.Zero; _1323_typeI < _hi19; _1323_typeI++) {
          DAST._ITypeArgDecl _1324_typeParam;
          _1324_typeParam = ((c).dtor_typeParams).Select(_1323_typeI);
          DAST._IType _1325_typeArg;
          RAST._ITypeParamDecl _1326_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(_1324_typeParam, out _out78, out _out79);
          _1325_typeArg = _out78;
          _1326_rTypeParamDecl = _out79;
          RAST._IType _1327_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1325_typeArg, DCOMP.GenTypeContext.@default());
          _1327_rTypeArg = _out80;
          _1322_types = Dafny.Sequence<RAST._IType>.Concat(_1322_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1327_rTypeArg))));
          if (((_1323_typeI) < (new BigInteger((_1281_variances).Count))) && (((_1281_variances).Select(_1323_typeI)).is_Nonvariant)) {
            _1316_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1316_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1327_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1328_coerceTypeParam;
          _1328_coerceTypeParam = Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_1324_typeParam, _pat_let9_0 => Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_pat_let9_0, _1329_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1323_typeI)), _pat_let10_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(_pat_let10_0, _1330_dt__update_hname_h0 => DAST.TypeArgDecl.create(_1330_dt__update_hname_h0, (_1329_dt__update__tmp_h0).dtor_bounds, (_1329_dt__update__tmp_h0).dtor_variance)))));
          DAST._IType _1331_coerceTypeArg;
          RAST._ITypeParamDecl _1332_rCoerceTypeParamDecl;
          DAST._IType _out81;
          RAST._ITypeParamDecl _out82;
          (this).GenTypeParam(_1328_coerceTypeParam, out _out81, out _out82);
          _1331_coerceTypeArg = _out81;
          _1332_rCoerceTypeParamDecl = _out82;
          _1319_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1319_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1325_typeArg, _1331_coerceTypeArg)));
          RAST._IType _1333_rCoerceType;
          RAST._IType _out83;
          _out83 = (this).GenType(_1331_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1333_rCoerceType = _out83;
          _1320_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1320_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1327_rTypeArg, _1333_rCoerceType)));
          _1316_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1316_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1333_rCoerceType));
          _1317_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1317_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1332_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1334_coerceFormal;
          _1334_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1323_typeI));
          _1321_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1321_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1327_rTypeArg, _1333_rCoerceType), (RAST.Expr.create_Identifier(_1334_coerceFormal)).Clone())));
          _1318_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1318_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1334_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1327_rTypeArg), _1333_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        _1280_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1280_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1335_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1335_tpe);
})), _1322_types)))));
      }
      bool _1336_cIsEq;
      _1336_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1336_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1279_datatypeName, _1277_rTypeParamsDecls, _1280_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1277_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1279_datatypeName), _1276_rTypeParams), _1278_whereConstraints, _1295_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1337_printImplBodyCases;
      _1337_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1338_hashImplBodyCases;
      _1338_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1339_coerceImplBodyCases;
      _1339_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi20 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1340_i = BigInteger.Zero; _1340_i < _hi20; _1340_i++) {
        DAST._IDatatypeCtor _1341_ctor;
        _1341_ctor = ((c).dtor_ctors).Select(_1340_i);
        Dafny.ISequence<Dafny.Rune> _1342_ctorMatch;
        _1342_ctorMatch = DCOMP.__default.escapeName((_1341_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1343_modulePrefix;
        _1343_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1344_ctorName;
        _1344_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1343_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1341_ctor).dtor_name));
        if (((new BigInteger((_1344_ctorName).Count)) >= (new BigInteger(13))) && (((_1344_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1344_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1345_printRhs;
        _1345_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1344_ctorName), (((_1341_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1346_hashRhs;
        _1346_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1347_coerceRhsArgs;
        _1347_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1348_isNumeric;
        _1348_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1349_ctorMatchInner;
        _1349_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi21 = new BigInteger(((_1341_ctor).dtor_args).Count);
        for (BigInteger _1350_j = BigInteger.Zero; _1350_j < _hi21; _1350_j++) {
          DAST._IDatatypeDtor _1351_dtor;
          _1351_dtor = ((_1341_ctor).dtor_args).Select(_1350_j);
          Dafny.ISequence<Dafny.Rune> _1352_patternName;
          _1352_patternName = DCOMP.__default.escapeDtor(((_1351_dtor).dtor_formal).dtor_name);
          Dafny.ISequence<Dafny.Rune> _1353_fieldName;
          _1353_fieldName = DCOMP.__default.escapeField(((_1351_dtor).dtor_formal).dtor_name);
          DAST._IType _1354_formalType;
          _1354_formalType = ((_1351_dtor).dtor_formal).dtor_typ;
          if (((_1350_j).Sign == 0) && ((_1353_fieldName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1348_isNumeric = true;
          }
          if (_1348_isNumeric) {
            _1353_fieldName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1351_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1350_j)));
          }
          _1346_hashRhs = (((_1354_formalType).is_Arrow) ? ((_1346_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))) : ((_1346_hashRhs).Then(((RAST.Expr.create_Identifier(_1353_fieldName)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))));
          _1349_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1349_ctorMatchInner, _1352_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1350_j).Sign == 1) {
            _1345_printRhs = (_1345_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1345_printRhs = (_1345_printRhs).Then(RAST.Expr.create_RawExpr((((_1354_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1353_fieldName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1355_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1356_formalTpe;
          RAST._IType _out84;
          _out84 = (this).GenType(_1354_formalType, DCOMP.GenTypeContext.@default());
          _1356_formalTpe = _out84;
          DAST._IType _1357_newFormalType;
          _1357_newFormalType = (_1354_formalType).Replace(_1319_coerceMap);
          RAST._IType _1358_newFormalTpe;
          _1358_newFormalTpe = (_1356_formalTpe).Replace(_1320_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1359_upcastConverter;
          _1359_upcastConverter = (this).UpcastConversionLambda(_1354_formalType, _1356_formalTpe, _1357_newFormalType, _1358_newFormalTpe, _1321_coerceMapToArg);
          if ((_1359_upcastConverter).is_Success) {
            RAST._IExpr _1360_coercionFunction;
            _1360_coercionFunction = (_1359_upcastConverter).dtor_value;
            _1355_coerceRhsArg = (_1360_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1352_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1350_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1279_datatypeName));
            _1355_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1347_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1347_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1352_patternName, _1355_coerceRhsArg)));
        }
        RAST._IExpr _1361_coerceRhs;
        _1361_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1279_datatypeName)).MSel(DCOMP.__default.escapeName((_1341_ctor).dtor_name)), _1347_coerceRhsArgs);
        if (_1348_isNumeric) {
          _1342_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1342_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1349_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1342_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1342_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1349_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1341_ctor).dtor_hasAnyArgs) {
          _1345_printRhs = (_1345_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1345_printRhs = (_1345_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1337_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1337_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1279_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1342_ctorMatch), RAST.Expr.create_Block(_1345_printRhs))));
        _1338_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1338_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1279_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1342_ctorMatch), RAST.Expr.create_Block(_1346_hashRhs))));
        _1339_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1339_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1279_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1342_ctorMatch), RAST.Expr.create_Block(_1361_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1362_extraCases;
        _1362_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1279_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _1337_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1337_printImplBodyCases, _1362_extraCases);
        _1338_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1338_hashImplBodyCases, _1362_extraCases);
        _1339_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1339_coerceImplBodyCases, _1362_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1363_defaultConstrainedTypeParams;
      _1363_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1277_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1364_rTypeParamsDeclsWithEq;
      _1364_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1277_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1365_rTypeParamsDeclsWithHash;
      _1365_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1277_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1366_printImplBody;
      _1366_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1337_printImplBodyCases);
      RAST._IExpr _1367_hashImplBody;
      _1367_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1338_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1277_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1279_datatypeName), _1276_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1277_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1279_datatypeName), _1276_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1366_printImplBody))))))));
      if ((new BigInteger((_1317_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1368_coerceImplBody;
        _1368_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1339_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1277_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1279_datatypeName), _1276_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1317_rCoerceTypeParams, _1318_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1279_datatypeName), _1276_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1279_datatypeName), _1316_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.Type.create_SelfOwned())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1279_datatypeName), _1316_coerceTypes)), _1368_coerceImplBody))))))))));
      }
      if (_1336_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1364_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1279_datatypeName), _1276_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1365_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1279_datatypeName), _1276_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1367_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1369_structName;
        _1369_structName = (RAST.Expr.create_Identifier(_1279_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1370_structAssignments;
        _1370_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi22 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1371_i = BigInteger.Zero; _1371_i < _hi22; _1371_i++) {
          DAST._IDatatypeDtor _1372_dtor;
          _1372_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1371_i);
          _1370_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1370_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1372_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1373_defaultConstrainedTypeParams;
        _1373_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1277_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1374_fullType;
        _1374_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1279_datatypeName), _1276_rTypeParams);
        if (_1336_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1373_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1374_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1374_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1369_structName, _1370_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1277_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1374_fullType), RAST.Type.create_Borrowed(_1374_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        for (BigInteger _1375_i = BigInteger.Zero; _1375_i < _hi23; _1375_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1375_i))));
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
        for (BigInteger _1376_i = BigInteger.Zero; _1376_i < _hi24; _1376_i++) {
          Dafny.ISequence<Dafny.Rune> _1377_id;
          _1377_id = ((p).Select(_1376_i));
          r = (r).MSel(((escape) ? (DCOMP.__default.escapeName(_1377_id)) : (DCOMP.__default.ReplaceDotByDoubleColon((_1377_id)))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi25 = new BigInteger((args).Count);
      for (BigInteger _1378_i = BigInteger.Zero; _1378_i < _hi25; _1378_i++) {
        RAST._IType _1379_genTp;
        RAST._IType _out85;
        _out85 = (this).GenType((args).Select(_1378_i), genTypeContext);
        _1379_genTp = _out85;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1379_genTp));
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, DCOMP._IGenTypeContext genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source64 = c;
      bool unmatched64 = true;
      if (unmatched64) {
        if (_source64.is_UserDefined) {
          DAST._IResolvedType _1380_resolved = _source64.dtor_resolved;
          unmatched64 = false;
          {
            RAST._IType _1381_t;
            RAST._IType _out86;
            _out86 = DCOMP.COMP.GenPath((_1380_resolved).dtor_path);
            _1381_t = _out86;
            Dafny.ISequence<RAST._IType> _1382_typeArgs;
            Dafny.ISequence<RAST._IType> _out87;
            _out87 = (this).GenTypeArgs((_1380_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _1383_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _1384_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1383_dt__update__tmp_h0).dtor_inBinding, (_1383_dt__update__tmp_h0).dtor_inFn, _1384_dt__update_hforTraitParents_h0))))));
            _1382_typeArgs = _out87;
            s = RAST.Type.create_TypeApp(_1381_t, _1382_typeArgs);
            DAST._IResolvedTypeBase _source65 = (_1380_resolved).dtor_kind;
            bool unmatched65 = true;
            if (unmatched65) {
              if (_source65.is_Class) {
                unmatched65 = false;
                {
                  s = (this).Object(s);
                }
              }
            }
            if (unmatched65) {
              if (_source65.is_Datatype) {
                unmatched65 = false;
                {
                  if ((this).IsRcWrapped((_1380_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched65) {
              if (_source65.is_Trait) {
                unmatched65 = false;
                {
                  if (((_1380_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched65) {
              DAST._IType _1385_t = _source65.dtor_baseType;
              DAST._INewtypeRange _1386_range = _source65.dtor_range;
              bool _1387_erased = _source65.dtor_erase;
              unmatched65 = false;
              {
                if (_1387_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source66 = DCOMP.COMP.NewtypeToRustType(_1385_t, _1386_range);
                  bool unmatched66 = true;
                  if (unmatched66) {
                    if (_source66.is_Some) {
                      RAST._IType _1388_v = _source66.dtor_value;
                      unmatched66 = false;
                      s = _1388_v;
                    }
                  }
                  if (unmatched66) {
                    unmatched66 = false;
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched64) {
        if (_source64.is_Object) {
          unmatched64 = false;
          {
            s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
            if (!((genTypeContext).dtor_forTraitParents)) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
        }
      }
      if (unmatched64) {
        if (_source64.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1389_types = _source64.dtor_Tuple_a0;
          unmatched64 = false;
          {
            Dafny.ISequence<RAST._IType> _1390_args;
            _1390_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1391_i;
            _1391_i = BigInteger.Zero;
            while ((_1391_i) < (new BigInteger((_1389_types).Count))) {
              RAST._IType _1392_generated;
              RAST._IType _out88;
              _out88 = (this).GenType((_1389_types).Select(_1391_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _1393_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _1394_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1393_dt__update__tmp_h1).dtor_inBinding, (_1393_dt__update__tmp_h1).dtor_inFn, _1394_dt__update_hforTraitParents_h1))))));
              _1392_generated = _out88;
              _1390_args = Dafny.Sequence<RAST._IType>.Concat(_1390_args, Dafny.Sequence<RAST._IType>.FromElements(_1392_generated));
              _1391_i = (_1391_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1389_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1390_args)) : (RAST.__default.SystemTupleType(_1390_args)));
          }
        }
      }
      if (unmatched64) {
        if (_source64.is_Array) {
          DAST._IType _1395_element = _source64.dtor_element;
          BigInteger _1396_dims = _source64.dtor_dims;
          unmatched64 = false;
          {
            if ((_1396_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1397_elem;
              RAST._IType _out89;
              _out89 = (this).GenType(_1395_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _1398_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _1399_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1398_dt__update__tmp_h2).dtor_inBinding, (_1398_dt__update__tmp_h2).dtor_inFn, _1399_dt__update_hforTraitParents_h2))))));
              _1397_elem = _out89;
              if ((_1396_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1397_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1400_n;
                _1400_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1396_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1400_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1397_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched64) {
        if (_source64.is_Seq) {
          DAST._IType _1401_element = _source64.dtor_element;
          unmatched64 = false;
          {
            RAST._IType _1402_elem;
            RAST._IType _out90;
            _out90 = (this).GenType(_1401_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _1403_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _1404_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1403_dt__update__tmp_h3).dtor_inBinding, (_1403_dt__update__tmp_h3).dtor_inFn, _1404_dt__update_hforTraitParents_h3))))));
            _1402_elem = _out90;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1402_elem));
          }
        }
      }
      if (unmatched64) {
        if (_source64.is_Set) {
          DAST._IType _1405_element = _source64.dtor_element;
          unmatched64 = false;
          {
            RAST._IType _1406_elem;
            RAST._IType _out91;
            _out91 = (this).GenType(_1405_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _1407_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _1408_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1407_dt__update__tmp_h4).dtor_inBinding, (_1407_dt__update__tmp_h4).dtor_inFn, _1408_dt__update_hforTraitParents_h4))))));
            _1406_elem = _out91;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1406_elem));
          }
        }
      }
      if (unmatched64) {
        if (_source64.is_Multiset) {
          DAST._IType _1409_element = _source64.dtor_element;
          unmatched64 = false;
          {
            RAST._IType _1410_elem;
            RAST._IType _out92;
            _out92 = (this).GenType(_1409_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _1411_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _1412_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1411_dt__update__tmp_h5).dtor_inBinding, (_1411_dt__update__tmp_h5).dtor_inFn, _1412_dt__update_hforTraitParents_h5))))));
            _1410_elem = _out92;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1410_elem));
          }
        }
      }
      if (unmatched64) {
        if (_source64.is_Map) {
          DAST._IType _1413_key = _source64.dtor_key;
          DAST._IType _1414_value = _source64.dtor_value;
          unmatched64 = false;
          {
            RAST._IType _1415_keyType;
            RAST._IType _out93;
            _out93 = (this).GenType(_1413_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _1416_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _1417_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1416_dt__update__tmp_h6).dtor_inBinding, (_1416_dt__update__tmp_h6).dtor_inFn, _1417_dt__update_hforTraitParents_h6))))));
            _1415_keyType = _out93;
            RAST._IType _1418_valueType;
            RAST._IType _out94;
            _out94 = (this).GenType(_1414_value, genTypeContext);
            _1418_valueType = _out94;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1415_keyType, _1418_valueType));
          }
        }
      }
      if (unmatched64) {
        if (_source64.is_MapBuilder) {
          DAST._IType _1419_key = _source64.dtor_key;
          DAST._IType _1420_value = _source64.dtor_value;
          unmatched64 = false;
          {
            RAST._IType _1421_keyType;
            RAST._IType _out95;
            _out95 = (this).GenType(_1419_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _1422_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _1423_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1422_dt__update__tmp_h7).dtor_inBinding, (_1422_dt__update__tmp_h7).dtor_inFn, _1423_dt__update_hforTraitParents_h7))))));
            _1421_keyType = _out95;
            RAST._IType _1424_valueType;
            RAST._IType _out96;
            _out96 = (this).GenType(_1420_value, genTypeContext);
            _1424_valueType = _out96;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1421_keyType, _1424_valueType));
          }
        }
      }
      if (unmatched64) {
        if (_source64.is_SetBuilder) {
          DAST._IType _1425_elem = _source64.dtor_element;
          unmatched64 = false;
          {
            RAST._IType _1426_elemType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1425_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _1427_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _1428_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1427_dt__update__tmp_h8).dtor_inBinding, (_1427_dt__update__tmp_h8).dtor_inFn, _1428_dt__update_hforTraitParents_h8))))));
            _1426_elemType = _out97;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1426_elemType));
          }
        }
      }
      if (unmatched64) {
        if (_source64.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1429_args = _source64.dtor_args;
          DAST._IType _1430_result = _source64.dtor_result;
          unmatched64 = false;
          {
            Dafny.ISequence<RAST._IType> _1431_argTypes;
            _1431_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1432_i;
            _1432_i = BigInteger.Zero;
            while ((_1432_i) < (new BigInteger((_1429_args).Count))) {
              RAST._IType _1433_generated;
              RAST._IType _out98;
              _out98 = (this).GenType((_1429_args).Select(_1432_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let29_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let29_0, _1434_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let30_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let30_0, _1435_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let31_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let31_0, _1436_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1434_dt__update__tmp_h9).dtor_inBinding, _1436_dt__update_hinFn_h0, _1435_dt__update_hforTraitParents_h9))))))));
              _1433_generated = _out98;
              _1431_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1431_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1433_generated)));
              _1432_i = (_1432_i) + (BigInteger.One);
            }
            RAST._IType _1437_resultType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1430_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1437_resultType = _out99;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1431_argTypes, _1437_resultType)));
          }
        }
      }
      if (unmatched64) {
        if (_source64.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source64.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1438_name = _h90;
          unmatched64 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1438_name));
        }
      }
      if (unmatched64) {
        if (_source64.is_Primitive) {
          DAST._IPrimitive _1439_p = _source64.dtor_Primitive_a0;
          unmatched64 = false;
          {
            DAST._IPrimitive _source67 = _1439_p;
            bool unmatched67 = true;
            if (unmatched67) {
              if (_source67.is_Int) {
                unmatched67 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
              }
            }
            if (unmatched67) {
              if (_source67.is_Real) {
                unmatched67 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
              }
            }
            if (unmatched67) {
              if (_source67.is_String) {
                unmatched67 = false;
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
              }
            }
            if (unmatched67) {
              if (_source67.is_Bool) {
                unmatched67 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched67) {
              unmatched67 = false;
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          }
        }
      }
      if (unmatched64) {
        Dafny.ISequence<Dafny.Rune> _1440_v = _source64.dtor_Passthrough_a0;
        unmatched64 = false;
        s = RAST.__default.RawType(_1440_v);
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
      for (BigInteger _1441_i = BigInteger.Zero; _1441_i < _hi26; _1441_i++) {
        DAST._IMethod _source68 = (body).Select(_1441_i);
        bool unmatched68 = true;
        if (unmatched68) {
          DAST._IMethod _1442_m = _source68;
          unmatched68 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source69 = (_1442_m).dtor_overridingPath;
            bool unmatched69 = true;
            if (unmatched69) {
              if (_source69.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1443_p = _source69.dtor_value;
                unmatched69 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1444_existing;
                  _1444_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1443_p)) {
                    _1444_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1443_p);
                  }
                  if (((new BigInteger(((_1442_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1445_genMethod;
                  RAST._IImplMember _out100;
                  _out100 = (this).GenMethod(_1442_m, true, enclosingType, enclosingTypeParams);
                  _1445_genMethod = _out100;
                  _1444_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1444_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1445_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1443_p, _1444_existing)));
                }
              }
            }
            if (unmatched69) {
              unmatched69 = false;
              {
                RAST._IImplMember _1446_generated;
                RAST._IImplMember _out101;
                _out101 = (this).GenMethod(_1442_m, forTrait, enclosingType, enclosingTypeParams);
                _1446_generated = _out101;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1446_generated));
              }
            }
          }
        }
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _hi27 = new BigInteger((@params).Count);
      for (BigInteger _1447_i = BigInteger.Zero; _1447_i < _hi27; _1447_i++) {
        DAST._IFormal _1448_param;
        _1448_param = (@params).Select(_1447_i);
        RAST._IType _1449_paramType;
        RAST._IType _out102;
        _out102 = (this).GenType((_1448_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1449_paramType = _out102;
        if ((!((_1449_paramType).CanReadWithoutClone())) && (!((_1448_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1449_paramType = RAST.Type.create_Borrowed(_1449_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1448_param).dtor_name), _1449_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1450_params;
      Dafny.ISequence<RAST._IFormal> _out103;
      _out103 = (this).GenParams((m).dtor_params);
      _1450_params = _out103;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1451_paramNames;
      _1451_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1452_paramTypes;
      _1452_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1453_paramI = BigInteger.Zero; _1453_paramI < _hi28; _1453_paramI++) {
        DAST._IFormal _1454_dafny__formal;
        _1454_dafny__formal = ((m).dtor_params).Select(_1453_paramI);
        RAST._IFormal _1455_formal;
        _1455_formal = (_1450_params).Select(_1453_paramI);
        Dafny.ISequence<Dafny.Rune> _1456_name;
        _1456_name = (_1455_formal).dtor_name;
        _1451_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1451_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1456_name));
        _1452_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1452_paramTypes, _1456_name, (_1455_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1457_fnName;
      _1457_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1458_selfIdent;
      _1458_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1459_selfId;
        _1459_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1459_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv139 = enclosingTypeParams;
        var _pat_let_tv140 = enclosingType;
        DAST._IType _1460_instanceType;
        _1460_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source70 = enclosingType;
          bool unmatched70 = true;
          if (unmatched70) {
            if (_source70.is_UserDefined) {
              DAST._IResolvedType _1461_r = _source70.dtor_resolved;
              unmatched70 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1461_r, _pat_let32_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let32_0, _1462_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv139, _pat_let33_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let33_0, _1463_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1462_dt__update__tmp_h0).dtor_path, _1463_dt__update_htypeArgs_h0, (_1462_dt__update__tmp_h0).dtor_kind, (_1462_dt__update__tmp_h0).dtor_attributes, (_1462_dt__update__tmp_h0).dtor_properMethods, (_1462_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched70) {
            unmatched70 = false;
            return _pat_let_tv140;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1464_selfFormal;
          _1464_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1450_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1464_selfFormal), _1450_params);
        } else {
          RAST._IType _1465_tpe;
          RAST._IType _out104;
          _out104 = (this).GenType(_1460_instanceType, DCOMP.GenTypeContext.@default());
          _1465_tpe = _out104;
          if ((_1459_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1465_tpe = RAST.Type.create_Borrowed(_1465_tpe);
          } else if ((_1459_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1465_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1465_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1465_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              _1465_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.Type.create_SelfOwned()));
            }
          }
          _1450_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1459_selfId, _1465_tpe)), _1450_params);
        }
        _1458_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1459_selfId, _1460_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1466_retTypeArgs;
      _1466_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1467_typeI;
      _1467_typeI = BigInteger.Zero;
      while ((_1467_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1468_typeExpr;
        RAST._IType _out105;
        _out105 = (this).GenType(((m).dtor_outTypes).Select(_1467_typeI), DCOMP.GenTypeContext.@default());
        _1468_typeExpr = _out105;
        _1466_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1466_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1468_typeExpr));
        _1467_typeI = (_1467_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1469_visibility;
      _1469_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1470_typeParamsFiltered;
      _1470_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi29 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1471_typeParamI = BigInteger.Zero; _1471_typeParamI < _hi29; _1471_typeParamI++) {
        DAST._ITypeArgDecl _1472_typeParam;
        _1472_typeParam = ((m).dtor_typeParams).Select(_1471_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1472_typeParam).dtor_name)))) {
          _1470_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1470_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1472_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1473_typeParams;
      _1473_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1470_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi30 = new BigInteger((_1470_typeParamsFiltered).Count);
        for (BigInteger _1474_i = BigInteger.Zero; _1474_i < _hi30; _1474_i++) {
          DAST._IType _1475_typeArg;
          RAST._ITypeParamDecl _1476_rTypeParamDecl;
          DAST._IType _out106;
          RAST._ITypeParamDecl _out107;
          (this).GenTypeParam((_1470_typeParamsFiltered).Select(_1474_i), out _out106, out _out107);
          _1475_typeArg = _out106;
          _1476_rTypeParamDecl = _out107;
          var _pat_let_tv141 = _1476_rTypeParamDecl;
          _1476_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1476_rTypeParamDecl, _pat_let34_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let34_0, _1477_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv141).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let35_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let35_0, _1478_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1477_dt__update__tmp_h1).dtor_content, _1478_dt__update_hconstraints_h0)))));
          _1473_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1473_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1476_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1479_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1480_env = DCOMP.Environment.Default();
      RAST._IExpr _1481_preBody;
      _1481_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1482_preAssignNames;
      _1482_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1483_preAssignTypes;
      _1483_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1484_earlyReturn;
        _1484_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source71 = (m).dtor_outVars;
        bool unmatched71 = true;
        if (unmatched71) {
          if (_source71.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1485_outVars = _source71.dtor_value;
            unmatched71 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1484_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi31 = new BigInteger((_1485_outVars).Count);
                for (BigInteger _1486_outI = BigInteger.Zero; _1486_outI < _hi31; _1486_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1487_outVar;
                  _1487_outVar = (_1485_outVars).Select(_1486_outI);
                  Dafny.ISequence<Dafny.Rune> _1488_outName;
                  _1488_outName = DCOMP.__default.escapeName((_1487_outVar));
                  Dafny.ISequence<Dafny.Rune> _1489_tracker__name;
                  _1489_tracker__name = DCOMP.__default.AddAssignedPrefix(_1488_outName);
                  _1482_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1482_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1489_tracker__name));
                  _1483_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1483_preAssignTypes, _1489_tracker__name, RAST.Type.create_Bool());
                  _1481_preBody = (_1481_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1489_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1490_tupleArgs;
                _1490_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi32 = new BigInteger((_1485_outVars).Count);
                for (BigInteger _1491_outI = BigInteger.Zero; _1491_outI < _hi32; _1491_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1492_outVar;
                  _1492_outVar = (_1485_outVars).Select(_1491_outI);
                  RAST._IType _1493_outType;
                  RAST._IType _out108;
                  _out108 = (this).GenType(((m).dtor_outTypes).Select(_1491_outI), DCOMP.GenTypeContext.@default());
                  _1493_outType = _out108;
                  Dafny.ISequence<Dafny.Rune> _1494_outName;
                  _1494_outName = DCOMP.__default.escapeName((_1492_outVar));
                  _1451_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1451_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1494_outName));
                  RAST._IType _1495_outMaybeType;
                  _1495_outMaybeType = (((_1493_outType).CanReadWithoutClone()) ? (_1493_outType) : (RAST.__default.MaybePlaceboType(_1493_outType)));
                  _1452_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1452_paramTypes, _1494_outName, _1495_outMaybeType);
                  _1490_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1490_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1494_outName));
                }
                _1484_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_1490_tupleArgs);
              }
            }
          }
        }
        if (unmatched71) {
          unmatched71 = false;
        }
        _1480_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1482_preAssignNames, _1451_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1483_preAssignTypes, _1452_paramTypes));
        RAST._IExpr _1496_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1497___v69;
        DCOMP._IEnvironment _1498___v70;
        RAST._IExpr _out109;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out110;
        DCOMP._IEnvironment _out111;
        (this).GenStmts((m).dtor_body, _1458_selfIdent, _1480_env, true, _1484_earlyReturn, out _out109, out _out110, out _out111);
        _1496_body = _out109;
        _1497___v69 = _out110;
        _1498___v70 = _out111;
        _1479_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1481_preBody).Then(_1496_body));
      } else {
        _1480_env = DCOMP.Environment.create(_1451_paramNames, _1452_paramTypes);
        _1479_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1469_visibility, RAST.Fn.create(_1457_fnName, _1473_typeParams, _1450_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1466_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1466_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1466_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1479_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1499_declarations;
      _1499_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1500_i;
      _1500_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1501_stmts;
      _1501_stmts = stmts;
      while ((_1500_i) < (new BigInteger((_1501_stmts).Count))) {
        DAST._IStatement _1502_stmt;
        _1502_stmt = (_1501_stmts).Select(_1500_i);
        DAST._IStatement _source72 = _1502_stmt;
        bool unmatched72 = true;
        if (unmatched72) {
          if (_source72.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1503_name = _source72.dtor_name;
            DAST._IType _1504_optType = _source72.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source72.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched72 = false;
              if (((_1500_i) + (BigInteger.One)) < (new BigInteger((_1501_stmts).Count))) {
                DAST._IStatement _source73 = (_1501_stmts).Select((_1500_i) + (BigInteger.One));
                bool unmatched73 = true;
                if (unmatched73) {
                  if (_source73.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source73.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _1505_name2 = ident0;
                      DAST._IExpression _1506_rhs = _source73.dtor_value;
                      unmatched73 = false;
                      if (object.Equals(_1505_name2, _1503_name)) {
                        _1501_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1501_stmts).Subsequence(BigInteger.Zero, _1500_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1503_name, _1504_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1506_rhs)))), (_1501_stmts).Drop((_1500_i) + (new BigInteger(2))));
                        _1502_stmt = (_1501_stmts).Select(_1500_i);
                      }
                    }
                  }
                }
                if (unmatched73) {
                  unmatched73 = false;
                }
              }
            }
          }
        }
        if (unmatched72) {
          unmatched72 = false;
        }
        RAST._IExpr _1507_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1508_recIdents;
        DCOMP._IEnvironment _1509_newEnv2;
        RAST._IExpr _out112;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out113;
        DCOMP._IEnvironment _out114;
        (this).GenStmt(_1502_stmt, selfIdent, newEnv, (isLast) && ((_1500_i) == ((new BigInteger((_1501_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out112, out _out113, out _out114);
        _1507_stmtExpr = _out112;
        _1508_recIdents = _out113;
        _1509_newEnv2 = _out114;
        newEnv = _1509_newEnv2;
        DAST._IStatement _source74 = _1502_stmt;
        bool unmatched74 = true;
        if (unmatched74) {
          if (_source74.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1510_name = _source74.dtor_name;
            unmatched74 = false;
            {
              _1499_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1499_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1510_name)));
            }
          }
        }
        if (unmatched74) {
          unmatched74 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1508_recIdents, _1499_declarations));
        generated = (generated).Then(_1507_stmtExpr);
        _1500_i = (_1500_i) + (BigInteger.One);
        if ((_1507_stmtExpr).is_Return) {
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
      DAST._IAssignLhs _source75 = lhs;
      bool unmatched75 = true;
      if (unmatched75) {
        if (_source75.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident1 = _source75.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _1511_id = ident1;
          unmatched75 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1512_idRust;
            _1512_idRust = DCOMP.__default.escapeName(_1511_id);
            if (((env).IsBorrowed(_1512_idRust)) || ((env).IsBorrowedMut(_1512_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1512_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1512_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1512_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched75) {
        if (_source75.is_Select) {
          DAST._IExpression _1513_on = _source75.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1514_field = _source75.dtor_field;
          unmatched75 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1515_fieldName;
            _1515_fieldName = DCOMP.__default.escapeName(_1514_field);
            RAST._IExpr _1516_onExpr;
            DCOMP._IOwnership _1517_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1518_recIdents;
            RAST._IExpr _out115;
            DCOMP._IOwnership _out116;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
            (this).GenExpr(_1513_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out115, out _out116, out _out117);
            _1516_onExpr = _out115;
            _1517_onOwned = _out116;
            _1518_recIdents = _out117;
            RAST._IExpr _source76 = _1516_onExpr;
            bool unmatched76 = true;
            if (unmatched76) {
              bool disjunctiveMatch11 = false;
              if (_source76.is_Call) {
                RAST._IExpr obj2 = _source76.dtor_obj;
                if (obj2.is_Select) {
                  RAST._IExpr obj3 = obj2.dtor_obj;
                  if (obj3.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name11 = obj3.dtor_name;
                    if (object.Equals(name11, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      Dafny.ISequence<Dafny.Rune> name12 = obj2.dtor_name;
                      if (object.Equals(name12, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                        disjunctiveMatch11 = true;
                      }
                    }
                  }
                }
              }
              if (_source76.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name13 = _source76.dtor_name;
                if (object.Equals(name13, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch11 = true;
                }
              }
              if (_source76.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op14 = _source76.dtor_op1;
                if (object.Equals(op14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying4 = _source76.dtor_underlying;
                  if (underlying4.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name14 = underlying4.dtor_name;
                    if (object.Equals(name14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      disjunctiveMatch11 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch11) {
                unmatched76 = false;
                Dafny.ISequence<Dafny.Rune> _1519_isAssignedVar;
                _1519_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1515_fieldName);
                if (((newEnv).dtor_names).Contains(_1519_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1515_fieldName), RAST.Expr.create_Identifier(_1519_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1519_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1519_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1515_fieldName, rhs);
                }
              }
            }
            if (unmatched76) {
              unmatched76 = false;
              if (!object.Equals(_1516_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1516_onExpr = ((this).modify__macro).Apply1(_1516_onExpr);
              }
              generated = RAST.__default.AssignMember(_1516_onExpr, _1515_fieldName, rhs);
            }
            readIdents = _1518_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched75) {
        DAST._IExpression _1520_on = _source75.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1521_indices = _source75.dtor_indices;
        unmatched75 = false;
        {
          RAST._IExpr _1522_onExpr;
          DCOMP._IOwnership _1523_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1524_recIdents;
          RAST._IExpr _out118;
          DCOMP._IOwnership _out119;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
          (this).GenExpr(_1520_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out118, out _out119, out _out120);
          _1522_onExpr = _out118;
          _1523_onOwned = _out119;
          _1524_recIdents = _out120;
          readIdents = _1524_recIdents;
          _1522_onExpr = ((this).modify__macro).Apply1(_1522_onExpr);
          RAST._IExpr _1525_r;
          _1525_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1526_indicesExpr;
          _1526_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi33 = new BigInteger((_1521_indices).Count);
          for (BigInteger _1527_i = BigInteger.Zero; _1527_i < _hi33; _1527_i++) {
            RAST._IExpr _1528_idx;
            DCOMP._IOwnership _1529___v79;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1530_recIdentsIdx;
            RAST._IExpr _out121;
            DCOMP._IOwnership _out122;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
            (this).GenExpr((_1521_indices).Select(_1527_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out121, out _out122, out _out123);
            _1528_idx = _out121;
            _1529___v79 = _out122;
            _1530_recIdentsIdx = _out123;
            Dafny.ISequence<Dafny.Rune> _1531_varName;
            _1531_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1527_i));
            _1526_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1526_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1531_varName)));
            _1525_r = (_1525_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1531_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1528_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1530_recIdentsIdx);
          }
          if ((new BigInteger((_1521_indices).Count)) > (BigInteger.One)) {
            _1522_onExpr = (_1522_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1532_rhs;
          _1532_rhs = rhs;
          var _pat_let_tv142 = env;
          if (((_1522_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1522_onExpr).LhsIdentifierName(), _pat_let36_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let36_0, _1533_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv142).GetType(_1533_name), _pat_let37_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let37_0, _1534_tpe => ((_1534_tpe).is_Some) && (((_1534_tpe).dtor_value).IsUninitArray())))))))) {
            _1532_rhs = RAST.__default.MaybeUninitNew(_1532_rhs);
          }
          generated = (_1525_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1522_onExpr, _1526_indicesExpr)), _1532_rhs));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source77 = stmt;
      bool unmatched77 = true;
      if (unmatched77) {
        if (_source77.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1535_fields = _source77.dtor_fields;
          unmatched77 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi34 = new BigInteger((_1535_fields).Count);
            for (BigInteger _1536_i = BigInteger.Zero; _1536_i < _hi34; _1536_i++) {
              DAST._IFormal _1537_field;
              _1537_field = (_1535_fields).Select(_1536_i);
              Dafny.ISequence<Dafny.Rune> _1538_fieldName;
              _1538_fieldName = DCOMP.__default.escapeName((_1537_field).dtor_name);
              RAST._IType _1539_fieldTyp;
              RAST._IType _out124;
              _out124 = (this).GenType((_1537_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1539_fieldTyp = _out124;
              Dafny.ISequence<Dafny.Rune> _1540_isAssignedVar;
              _1540_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1538_fieldName);
              if (((newEnv).dtor_names).Contains(_1540_isAssignedVar)) {
                RAST._IExpr _1541_rhs;
                DCOMP._IOwnership _1542___v80;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1543___v81;
                RAST._IExpr _out125;
                DCOMP._IOwnership _out126;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out127;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1537_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out125, out _out126, out _out127);
                _1541_rhs = _out125;
                _1542___v80 = _out126;
                _1543___v81 = _out127;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1540_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1538_fieldName), RAST.Expr.create_Identifier(_1540_isAssignedVar), _1541_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1540_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1544_name = _source77.dtor_name;
          DAST._IType _1545_typ = _source77.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source77.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1546_expression = maybeValue1.dtor_value;
            unmatched77 = false;
            {
              RAST._IType _1547_tpe;
              RAST._IType _out128;
              _out128 = (this).GenType(_1545_typ, DCOMP.GenTypeContext.InBinding());
              _1547_tpe = _out128;
              Dafny.ISequence<Dafny.Rune> _1548_varName;
              _1548_varName = DCOMP.__default.escapeName(_1544_name);
              bool _1549_hasCopySemantics;
              _1549_hasCopySemantics = (_1547_tpe).CanReadWithoutClone();
              if (((_1546_expression).is_InitializationValue) && (!(_1549_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1548_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1547_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1548_varName, RAST.__default.MaybePlaceboType(_1547_tpe));
              } else {
                RAST._IExpr _1550_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1551_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1546_expression).is_InitializationValue) && ((_1547_tpe).IsObjectOrPointer())) {
                  _1550_expr = (_1547_tpe).ToNullExpr();
                  _1551_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1552_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out129;
                  DCOMP._IOwnership _out130;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
                  (this).GenExpr(_1546_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out129, out _out130, out _out131);
                  _1550_expr = _out129;
                  _1552_exprOwnership = _out130;
                  _1551_recIdents = _out131;
                }
                readIdents = _1551_recIdents;
                _1547_tpe = (((_1546_expression).is_NewUninitArray) ? ((_1547_tpe).TypeAtInitialization()) : (_1547_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1544_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1547_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1550_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1544_name), _1547_tpe);
              }
            }
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1553_name = _source77.dtor_name;
          DAST._IType _1554_typ = _source77.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source77.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched77 = false;
            {
              DAST._IStatement _1555_newStmt;
              _1555_newStmt = DAST.Statement.create_DeclareVar(_1553_name, _1554_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1554_typ)));
              RAST._IExpr _out132;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out133;
              DCOMP._IEnvironment _out134;
              (this).GenStmt(_1555_newStmt, selfIdent, env, isLast, earlyReturn, out _out132, out _out133, out _out134);
              generated = _out132;
              readIdents = _out133;
              newEnv = _out134;
            }
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Assign) {
          DAST._IAssignLhs _1556_lhs = _source77.dtor_lhs;
          DAST._IExpression _1557_expression = _source77.dtor_value;
          unmatched77 = false;
          {
            RAST._IExpr _1558_exprGen;
            DCOMP._IOwnership _1559___v82;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1560_exprIdents;
            RAST._IExpr _out135;
            DCOMP._IOwnership _out136;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
            (this).GenExpr(_1557_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out135, out _out136, out _out137);
            _1558_exprGen = _out135;
            _1559___v82 = _out136;
            _1560_exprIdents = _out137;
            if ((_1556_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1561_rustId;
              _1561_rustId = DCOMP.__default.escapeName(((_1556_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1562_tpe;
              _1562_tpe = (env).GetType(_1561_rustId);
              if (((_1562_tpe).is_Some) && ((((_1562_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1558_exprGen = RAST.__default.MaybePlacebo(_1558_exprGen);
              }
            }
            if (((_1556_lhs).is_Index) && (((_1556_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1563_rustId;
              _1563_rustId = DCOMP.__default.escapeName(((_1556_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1564_tpe;
              _1564_tpe = (env).GetType(_1563_rustId);
              if (((_1564_tpe).is_Some) && ((((_1564_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1558_exprGen = RAST.__default.MaybeUninitNew(_1558_exprGen);
              }
            }
            RAST._IExpr _1565_lhsGen;
            bool _1566_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1567_recIdents;
            DCOMP._IEnvironment _1568_resEnv;
            RAST._IExpr _out138;
            bool _out139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
            DCOMP._IEnvironment _out141;
            (this).GenAssignLhs(_1556_lhs, _1558_exprGen, selfIdent, env, out _out138, out _out139, out _out140, out _out141);
            _1565_lhsGen = _out138;
            _1566_needsIIFE = _out139;
            _1567_recIdents = _out140;
            _1568_resEnv = _out141;
            generated = _1565_lhsGen;
            newEnv = _1568_resEnv;
            if (_1566_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1567_recIdents, _1560_exprIdents);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_If) {
          DAST._IExpression _1569_cond = _source77.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1570_thnDafny = _source77.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1571_elsDafny = _source77.dtor_els;
          unmatched77 = false;
          {
            RAST._IExpr _1572_cond;
            DCOMP._IOwnership _1573___v83;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1574_recIdents;
            RAST._IExpr _out142;
            DCOMP._IOwnership _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            (this).GenExpr(_1569_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out142, out _out143, out _out144);
            _1572_cond = _out142;
            _1573___v83 = _out143;
            _1574_recIdents = _out144;
            Dafny.ISequence<Dafny.Rune> _1575_condString;
            _1575_condString = (_1572_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1574_recIdents;
            RAST._IExpr _1576_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1577_thnIdents;
            DCOMP._IEnvironment _1578_thnEnv;
            RAST._IExpr _out145;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out146;
            DCOMP._IEnvironment _out147;
            (this).GenStmts(_1570_thnDafny, selfIdent, env, isLast, earlyReturn, out _out145, out _out146, out _out147);
            _1576_thn = _out145;
            _1577_thnIdents = _out146;
            _1578_thnEnv = _out147;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1577_thnIdents);
            RAST._IExpr _1579_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1580_elsIdents;
            DCOMP._IEnvironment _1581_elsEnv;
            RAST._IExpr _out148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
            DCOMP._IEnvironment _out150;
            (this).GenStmts(_1571_elsDafny, selfIdent, env, isLast, earlyReturn, out _out148, out _out149, out _out150);
            _1579_els = _out148;
            _1580_elsIdents = _out149;
            _1581_elsEnv = _out150;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1580_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1572_cond, _1576_thn, _1579_els);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1582_lbl = _source77.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1583_body = _source77.dtor_body;
          unmatched77 = false;
          {
            RAST._IExpr _1584_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1585_bodyIdents;
            DCOMP._IEnvironment _1586_env2;
            RAST._IExpr _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP._IEnvironment _out153;
            (this).GenStmts(_1583_body, selfIdent, env, isLast, earlyReturn, out _out151, out _out152, out _out153);
            _1584_body = _out151;
            _1585_bodyIdents = _out152;
            _1586_env2 = _out153;
            readIdents = _1585_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1582_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1584_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_While) {
          DAST._IExpression _1587_cond = _source77.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1588_body = _source77.dtor_body;
          unmatched77 = false;
          {
            RAST._IExpr _1589_cond;
            DCOMP._IOwnership _1590___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1591_recIdents;
            RAST._IExpr _out154;
            DCOMP._IOwnership _out155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
            (this).GenExpr(_1587_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out154, out _out155, out _out156);
            _1589_cond = _out154;
            _1590___v84 = _out155;
            _1591_recIdents = _out156;
            readIdents = _1591_recIdents;
            RAST._IExpr _1592_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1593_bodyIdents;
            DCOMP._IEnvironment _1594_bodyEnv;
            RAST._IExpr _out157;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out158;
            DCOMP._IEnvironment _out159;
            (this).GenStmts(_1588_body, selfIdent, env, false, earlyReturn, out _out157, out _out158, out _out159);
            _1592_bodyExpr = _out157;
            _1593_bodyIdents = _out158;
            _1594_bodyEnv = _out159;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1593_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1589_cond), _1592_bodyExpr);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1595_boundName = _source77.dtor_boundName;
          DAST._IType _1596_boundType = _source77.dtor_boundType;
          DAST._IExpression _1597_overExpr = _source77.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1598_body = _source77.dtor_body;
          unmatched77 = false;
          {
            RAST._IExpr _1599_over;
            DCOMP._IOwnership _1600___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1601_recIdents;
            RAST._IExpr _out160;
            DCOMP._IOwnership _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            (this).GenExpr(_1597_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out160, out _out161, out _out162);
            _1599_over = _out160;
            _1600___v85 = _out161;
            _1601_recIdents = _out162;
            if (((_1597_overExpr).is_MapBoundedPool) || ((_1597_overExpr).is_SetBoundedPool)) {
              _1599_over = ((_1599_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1602_boundTpe;
            RAST._IType _out163;
            _out163 = (this).GenType(_1596_boundType, DCOMP.GenTypeContext.@default());
            _1602_boundTpe = _out163;
            readIdents = _1601_recIdents;
            Dafny.ISequence<Dafny.Rune> _1603_boundRName;
            _1603_boundRName = DCOMP.__default.escapeName(_1595_boundName);
            RAST._IExpr _1604_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1605_bodyIdents;
            DCOMP._IEnvironment _1606_bodyEnv;
            RAST._IExpr _out164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
            DCOMP._IEnvironment _out166;
            (this).GenStmts(_1598_body, selfIdent, (env).AddAssigned(_1603_boundRName, _1602_boundTpe), false, earlyReturn, out _out164, out _out165, out _out166);
            _1604_bodyExpr = _out164;
            _1605_bodyIdents = _out165;
            _1606_bodyEnv = _out166;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1605_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1603_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1603_boundRName, _1599_over, _1604_bodyExpr);
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1607_toLabel = _source77.dtor_toLabel;
          unmatched77 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source78 = _1607_toLabel;
            bool unmatched78 = true;
            if (unmatched78) {
              if (_source78.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1608_lbl = _source78.dtor_value;
                unmatched78 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1608_lbl)));
                }
              }
            }
            if (unmatched78) {
              unmatched78 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1609_body = _source77.dtor_body;
          unmatched77 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1610_selfClone;
              DCOMP._IOwnership _1611___v86;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1612___v87;
              RAST._IExpr _out167;
              DCOMP._IOwnership _out168;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out167, out _out168, out _out169);
              _1610_selfClone = _out167;
              _1611___v86 = _out168;
              _1612___v87 = _out169;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1610_selfClone)));
            }
            newEnv = env;
            BigInteger _hi35 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1613_paramI = BigInteger.Zero; _1613_paramI < _hi35; _1613_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1614_param;
              _1614_param = ((env).dtor_names).Select(_1613_paramI);
              RAST._IExpr _1615_paramInit;
              DCOMP._IOwnership _1616___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1617___v89;
              RAST._IExpr _out170;
              DCOMP._IOwnership _out171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out172;
              (this).GenIdent(_1614_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out170, out _out171, out _out172);
              _1615_paramInit = _out170;
              _1616___v88 = _out171;
              _1617___v89 = _out172;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1614_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1615_paramInit)));
              if (((env).dtor_types).Contains(_1614_param)) {
                RAST._IType _1618_declaredType;
                _1618_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1614_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1614_param, _1618_declaredType);
              }
            }
            RAST._IExpr _1619_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1620_bodyIdents;
            DCOMP._IEnvironment _1621_bodyEnv;
            RAST._IExpr _out173;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out174;
            DCOMP._IEnvironment _out175;
            (this).GenStmts(_1609_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out173, out _out174, out _out175);
            _1619_bodyExpr = _out173;
            _1620_bodyIdents = _out174;
            _1621_bodyEnv = _out175;
            readIdents = _1620_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1619_bodyExpr)));
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_JumpTailCallStart) {
          unmatched77 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Call) {
          DAST._IExpression _1622_on = _source77.dtor_on;
          DAST._ICallName _1623_name = _source77.dtor_callName;
          Dafny.ISequence<DAST._IType> _1624_typeArgs = _source77.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1625_args = _source77.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1626_maybeOutVars = _source77.dtor_outs;
          unmatched77 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1627_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1628_recIdents;
            Dafny.ISequence<RAST._IType> _1629_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1630_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
            Dafny.ISequence<RAST._IType> _out178;
            Std.Wrappers._IOption<DAST._IResolvedType> _out179;
            (this).GenArgs(selfIdent, _1623_name, _1624_typeArgs, _1625_args, env, out _out176, out _out177, out _out178, out _out179);
            _1627_argExprs = _out176;
            _1628_recIdents = _out177;
            _1629_typeExprs = _out178;
            _1630_fullNameQualifier = _out179;
            readIdents = _1628_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source79 = _1630_fullNameQualifier;
            bool unmatched79 = true;
            if (unmatched79) {
              if (_source79.is_Some) {
                DAST._IResolvedType value9 = _source79.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1631_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1632_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1633_base = value9.dtor_kind;
                unmatched79 = false;
                RAST._IExpr _1634_fullPath;
                RAST._IExpr _out180;
                _out180 = DCOMP.COMP.GenPathExpr(_1631_path, true);
                _1634_fullPath = _out180;
                Dafny.ISequence<RAST._IType> _1635_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out181;
                _out181 = (this).GenTypeArgs(_1632_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1635_onTypeExprs = _out181;
                RAST._IExpr _1636_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1637_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1638_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1633_base).is_Trait) || ((_1633_base).is_Class)) {
                  RAST._IExpr _out182;
                  DCOMP._IOwnership _out183;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out184;
                  (this).GenExpr(_1622_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out182, out _out183, out _out184);
                  _1636_onExpr = _out182;
                  _1637_recOwnership = _out183;
                  _1638_recIdents = _out184;
                  _1636_onExpr = ((this).modify__macro).Apply1(_1636_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1638_recIdents);
                } else {
                  RAST._IExpr _out185;
                  DCOMP._IOwnership _out186;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out187;
                  (this).GenExpr(_1622_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out185, out _out186, out _out187);
                  _1636_onExpr = _out185;
                  _1637_recOwnership = _out186;
                  _1638_recIdents = _out187;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1638_recIdents);
                }
                generated = ((((_1634_fullPath).ApplyType(_1635_onTypeExprs)).MSel(DCOMP.__default.escapeName((_1623_name).dtor_name))).ApplyType(_1629_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1636_onExpr), _1627_argExprs));
              }
            }
            if (unmatched79) {
              unmatched79 = false;
              RAST._IExpr _1639_onExpr;
              DCOMP._IOwnership _1640___v94;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1641_enclosingIdents;
              RAST._IExpr _out188;
              DCOMP._IOwnership _out189;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
              (this).GenExpr(_1622_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out188, out _out189, out _out190);
              _1639_onExpr = _out188;
              _1640___v94 = _out189;
              _1641_enclosingIdents = _out190;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1641_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1642_renderedName;
              _1642_renderedName = (this).GetMethodName(_1622_on, _1623_name);
              DAST._IExpression _source80 = _1622_on;
              bool unmatched80 = true;
              if (unmatched80) {
                bool disjunctiveMatch12 = false;
                if (_source80.is_Companion) {
                  disjunctiveMatch12 = true;
                }
                if (_source80.is_ExternCompanion) {
                  disjunctiveMatch12 = true;
                }
                if (disjunctiveMatch12) {
                  unmatched80 = false;
                  {
                    _1639_onExpr = (_1639_onExpr).MSel(_1642_renderedName);
                  }
                }
              }
              if (unmatched80) {
                unmatched80 = false;
                {
                  if (!object.Equals(_1639_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source81 = _1623_name;
                    bool unmatched81 = true;
                    if (unmatched81) {
                      if (_source81.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source81.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1643_tpe = onType0.dtor_value;
                          unmatched81 = false;
                          RAST._IType _1644_typ;
                          RAST._IType _out191;
                          _out191 = (this).GenType(_1643_tpe, DCOMP.GenTypeContext.@default());
                          _1644_typ = _out191;
                          if (((_1644_typ).IsObjectOrPointer()) && (!object.Equals(_1639_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1639_onExpr = ((this).modify__macro).Apply1(_1639_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched81) {
                      unmatched81 = false;
                    }
                  }
                  _1639_onExpr = (_1639_onExpr).Sel(_1642_renderedName);
                }
              }
              generated = ((_1639_onExpr).ApplyType(_1629_typeExprs)).Apply(_1627_argExprs);
            }
            if (((_1626_maybeOutVars).is_Some) && ((new BigInteger(((_1626_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1645_outVar;
              _1645_outVar = DCOMP.__default.escapeName((((_1626_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1645_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1645_outVar, generated);
            } else if (((_1626_maybeOutVars).is_None) || ((new BigInteger(((_1626_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1646_tmpVar;
              _1646_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1647_tmpId;
              _1647_tmpId = RAST.Expr.create_Identifier(_1646_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1646_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1648_outVars;
              _1648_outVars = (_1626_maybeOutVars).dtor_value;
              BigInteger _hi36 = new BigInteger((_1648_outVars).Count);
              for (BigInteger _1649_outI = BigInteger.Zero; _1649_outI < _hi36; _1649_outI++) {
                Dafny.ISequence<Dafny.Rune> _1650_outVar;
                _1650_outVar = DCOMP.__default.escapeName(((_1648_outVars).Select(_1649_outI)));
                RAST._IExpr _1651_rhs;
                _1651_rhs = (_1647_tmpId).Sel(Std.Strings.__default.OfNat(_1649_outI));
                if (!((env).CanReadWithoutClone(_1650_outVar))) {
                  _1651_rhs = RAST.__default.MaybePlacebo(_1651_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1650_outVar, _1651_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Return) {
          DAST._IExpression _1652_exprDafny = _source77.dtor_expr;
          unmatched77 = false;
          {
            RAST._IExpr _1653_expr;
            DCOMP._IOwnership _1654___v103;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1655_recIdents;
            RAST._IExpr _out192;
            DCOMP._IOwnership _out193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
            (this).GenExpr(_1652_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out192, out _out193, out _out194);
            _1653_expr = _out192;
            _1654___v103 = _out193;
            _1655_recIdents = _out194;
            readIdents = _1655_recIdents;
            if (isLast) {
              generated = _1653_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1653_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_EarlyReturn) {
          unmatched77 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source82 = earlyReturn;
            bool unmatched82 = true;
            if (unmatched82) {
              if (_source82.is_None) {
                unmatched82 = false;
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
              }
            }
            if (unmatched82) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1656_rustIdents = _source82.dtor_value;
              unmatched82 = false;
              Dafny.ISequence<RAST._IExpr> _1657_tupleArgs;
              _1657_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi37 = new BigInteger((_1656_rustIdents).Count);
              for (BigInteger _1658_i = BigInteger.Zero; _1658_i < _hi37; _1658_i++) {
                RAST._IExpr _1659_rIdent;
                DCOMP._IOwnership _1660___v104;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1661___v105;
                RAST._IExpr _out195;
                DCOMP._IOwnership _out196;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
                (this).GenIdent((_1656_rustIdents).Select(_1658_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out195, out _out196, out _out197);
                _1659_rIdent = _out195;
                _1660___v104 = _out196;
                _1661___v105 = _out197;
                _1657_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1657_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1659_rIdent));
              }
              if ((new BigInteger((_1657_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1657_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1657_tupleArgs)));
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Halt) {
          unmatched77 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched77) {
        DAST._IExpression _1662_e = _source77.dtor_Print_a0;
        unmatched77 = false;
        {
          RAST._IExpr _1663_printedExpr;
          DCOMP._IOwnership _1664_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1665_recIdents;
          RAST._IExpr _out198;
          DCOMP._IOwnership _out199;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out200;
          (this).GenExpr(_1662_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out198, out _out199, out _out200);
          _1663_printedExpr = _out198;
          _1664_recOwnership = _out199;
          _1665_recIdents = _out200;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1663_printedExpr)));
          readIdents = _1665_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source83 = range;
      bool unmatched83 = true;
      if (unmatched83) {
        if (_source83.is_NoRange) {
          unmatched83 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched83) {
        if (_source83.is_U8) {
          unmatched83 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched83) {
        if (_source83.is_U16) {
          unmatched83 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched83) {
        if (_source83.is_U32) {
          unmatched83 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched83) {
        if (_source83.is_U64) {
          unmatched83 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched83) {
        if (_source83.is_U128) {
          unmatched83 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched83) {
        if (_source83.is_I8) {
          unmatched83 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched83) {
        if (_source83.is_I16) {
          unmatched83 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched83) {
        if (_source83.is_I32) {
          unmatched83 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched83) {
        if (_source83.is_I64) {
          unmatched83 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched83) {
        if (_source83.is_I128) {
          unmatched83 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched83) {
        unmatched83 = false;
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
        RAST._IExpr _out201;
        DCOMP._IOwnership _out202;
        (this).FromOwned(r, expectedOwnership, out _out201, out _out202);
        @out = _out201;
        resultingOwnership = _out202;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out203;
        DCOMP._IOwnership _out204;
        (this).FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out203, out _out204);
        @out = _out203;
        resultingOwnership = _out204;
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
      DAST._IExpression _source84 = e;
      bool unmatched84 = true;
      if (unmatched84) {
        if (_source84.is_Literal) {
          DAST._ILiteral _h170 = _source84.dtor_Literal_a0;
          if (_h170.is_BoolLiteral) {
            bool _1666_b = _h170.dtor_BoolLiteral_a0;
            unmatched84 = false;
            {
              RAST._IExpr _out205;
              DCOMP._IOwnership _out206;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1666_b), expectedOwnership, out _out205, out _out206);
              r = _out205;
              resultingOwnership = _out206;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Literal) {
          DAST._ILiteral _h171 = _source84.dtor_Literal_a0;
          if (_h171.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1667_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1668_t = _h171.dtor_IntLiteral_a1;
            unmatched84 = false;
            {
              DAST._IType _source85 = _1668_t;
              bool unmatched85 = true;
              if (unmatched85) {
                if (_source85.is_Primitive) {
                  DAST._IPrimitive _h70 = _source85.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched85 = false;
                    {
                      if ((new BigInteger((_1667_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1667_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1667_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched85) {
                DAST._IType _1669_o = _source85;
                unmatched85 = false;
                {
                  RAST._IType _1670_genType;
                  RAST._IType _out207;
                  _out207 = (this).GenType(_1669_o, DCOMP.GenTypeContext.@default());
                  _1670_genType = _out207;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1667_i), _1670_genType);
                }
              }
              RAST._IExpr _out208;
              DCOMP._IOwnership _out209;
              (this).FromOwned(r, expectedOwnership, out _out208, out _out209);
              r = _out208;
              resultingOwnership = _out209;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Literal) {
          DAST._ILiteral _h172 = _source84.dtor_Literal_a0;
          if (_h172.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1671_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1672_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1673_t = _h172.dtor_DecLiteral_a2;
            unmatched84 = false;
            {
              DAST._IType _source86 = _1673_t;
              bool unmatched86 = true;
              if (unmatched86) {
                if (_source86.is_Primitive) {
                  DAST._IPrimitive _h71 = _source86.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched86 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1671_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1672_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched86) {
                DAST._IType _1674_o = _source86;
                unmatched86 = false;
                {
                  RAST._IType _1675_genType;
                  RAST._IType _out210;
                  _out210 = (this).GenType(_1674_o, DCOMP.GenTypeContext.@default());
                  _1675_genType = _out210;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1671_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1672_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1675_genType);
                }
              }
              RAST._IExpr _out211;
              DCOMP._IOwnership _out212;
              (this).FromOwned(r, expectedOwnership, out _out211, out _out212);
              r = _out211;
              resultingOwnership = _out212;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Literal) {
          DAST._ILiteral _h173 = _source84.dtor_Literal_a0;
          if (_h173.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1676_l = _h173.dtor_StringLiteral_a0;
            bool _1677_verbatim = _h173.dtor_verbatim;
            unmatched84 = false;
            {
              if (_1677_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1676_l, false, _1677_verbatim));
              RAST._IExpr _out213;
              DCOMP._IOwnership _out214;
              (this).FromOwned(r, expectedOwnership, out _out213, out _out214);
              r = _out213;
              resultingOwnership = _out214;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Literal) {
          DAST._ILiteral _h174 = _source84.dtor_Literal_a0;
          if (_h174.is_CharLiteralUTF16) {
            BigInteger _1678_c = _h174.dtor_CharLiteralUTF16_a0;
            unmatched84 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1678_c));
              r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out215;
              DCOMP._IOwnership _out216;
              (this).FromOwned(r, expectedOwnership, out _out215, out _out216);
              r = _out215;
              resultingOwnership = _out216;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched84) {
        if (_source84.is_Literal) {
          DAST._ILiteral _h175 = _source84.dtor_Literal_a0;
          if (_h175.is_CharLiteral) {
            Dafny.Rune _1679_c = _h175.dtor_CharLiteral_a0;
            unmatched84 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1679_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
              RAST._IExpr _out217;
              DCOMP._IOwnership _out218;
              (this).FromOwned(r, expectedOwnership, out _out217, out _out218);
              r = _out217;
              resultingOwnership = _out218;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched84) {
        DAST._ILiteral _h176 = _source84.dtor_Literal_a0;
        DAST._IType _1680_tpe = _h176.dtor_Null_a0;
        unmatched84 = false;
        {
          RAST._IType _1681_tpeGen;
          RAST._IType _out219;
          _out219 = (this).GenType(_1680_tpe, DCOMP.GenTypeContext.@default());
          _1681_tpeGen = _out219;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"));
          } else {
            r = RAST.Expr.create_TypeAscription(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1681_tpeGen);
          }
          RAST._IExpr _out220;
          DCOMP._IOwnership _out221;
          (this).FromOwned(r, expectedOwnership, out _out220, out _out221);
          r = _out220;
          resultingOwnership = _out221;
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
      DAST._IBinOp _1682_op = _let_tmp_rhs54.dtor_op;
      DAST._IExpression _1683_lExpr = _let_tmp_rhs54.dtor_left;
      DAST._IExpression _1684_rExpr = _let_tmp_rhs54.dtor_right;
      DAST.Format._IBinaryOpFormat _1685_format = _let_tmp_rhs54.dtor_format2;
      bool _1686_becomesLeftCallsRight;
      _1686_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source87 = _1682_op;
        bool unmatched87 = true;
        if (unmatched87) {
          bool disjunctiveMatch13 = false;
          if (_source87.is_SetMerge) {
            disjunctiveMatch13 = true;
          }
          if (_source87.is_SetSubtraction) {
            disjunctiveMatch13 = true;
          }
          if (_source87.is_SetIntersection) {
            disjunctiveMatch13 = true;
          }
          if (_source87.is_SetDisjoint) {
            disjunctiveMatch13 = true;
          }
          if (_source87.is_MapMerge) {
            disjunctiveMatch13 = true;
          }
          if (_source87.is_MapSubtraction) {
            disjunctiveMatch13 = true;
          }
          if (_source87.is_MultisetMerge) {
            disjunctiveMatch13 = true;
          }
          if (_source87.is_MultisetSubtraction) {
            disjunctiveMatch13 = true;
          }
          if (_source87.is_MultisetIntersection) {
            disjunctiveMatch13 = true;
          }
          if (_source87.is_MultisetDisjoint) {
            disjunctiveMatch13 = true;
          }
          if (_source87.is_Concat) {
            disjunctiveMatch13 = true;
          }
          if (disjunctiveMatch13) {
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
      bool _1687_becomesRightCallsLeft;
      _1687_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source88 = _1682_op;
        bool unmatched88 = true;
        if (unmatched88) {
          if (_source88.is_In) {
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
      bool _1688_becomesCallLeftRight;
      _1688_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source89 = _1682_op;
        bool unmatched89 = true;
        if (unmatched89) {
          if (_source89.is_Eq) {
            bool referential0 = _source89.dtor_referential;
            if ((referential0) == (true)) {
              unmatched89 = false;
              return false;
            }
          }
        }
        if (unmatched89) {
          if (_source89.is_SetMerge) {
            unmatched89 = false;
            return true;
          }
        }
        if (unmatched89) {
          if (_source89.is_SetSubtraction) {
            unmatched89 = false;
            return true;
          }
        }
        if (unmatched89) {
          if (_source89.is_SetIntersection) {
            unmatched89 = false;
            return true;
          }
        }
        if (unmatched89) {
          if (_source89.is_SetDisjoint) {
            unmatched89 = false;
            return true;
          }
        }
        if (unmatched89) {
          if (_source89.is_MapMerge) {
            unmatched89 = false;
            return true;
          }
        }
        if (unmatched89) {
          if (_source89.is_MapSubtraction) {
            unmatched89 = false;
            return true;
          }
        }
        if (unmatched89) {
          if (_source89.is_MultisetMerge) {
            unmatched89 = false;
            return true;
          }
        }
        if (unmatched89) {
          if (_source89.is_MultisetSubtraction) {
            unmatched89 = false;
            return true;
          }
        }
        if (unmatched89) {
          if (_source89.is_MultisetIntersection) {
            unmatched89 = false;
            return true;
          }
        }
        if (unmatched89) {
          if (_source89.is_MultisetDisjoint) {
            unmatched89 = false;
            return true;
          }
        }
        if (unmatched89) {
          if (_source89.is_Concat) {
            unmatched89 = false;
            return true;
          }
        }
        if (unmatched89) {
          unmatched89 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1689_expectedLeftOwnership;
      _1689_expectedLeftOwnership = ((_1686_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1687_becomesRightCallsLeft) || (_1688_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1690_expectedRightOwnership;
      _1690_expectedRightOwnership = (((_1686_becomesLeftCallsRight) || (_1688_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1687_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1691_left;
      DCOMP._IOwnership _1692___v110;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1693_recIdentsL;
      RAST._IExpr _out222;
      DCOMP._IOwnership _out223;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out224;
      (this).GenExpr(_1683_lExpr, selfIdent, env, _1689_expectedLeftOwnership, out _out222, out _out223, out _out224);
      _1691_left = _out222;
      _1692___v110 = _out223;
      _1693_recIdentsL = _out224;
      RAST._IExpr _1694_right;
      DCOMP._IOwnership _1695___v111;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1696_recIdentsR;
      RAST._IExpr _out225;
      DCOMP._IOwnership _out226;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
      (this).GenExpr(_1684_rExpr, selfIdent, env, _1690_expectedRightOwnership, out _out225, out _out226, out _out227);
      _1694_right = _out225;
      _1695___v111 = _out226;
      _1696_recIdentsR = _out227;
      DAST._IBinOp _source90 = _1682_op;
      bool unmatched90 = true;
      if (unmatched90) {
        if (_source90.is_In) {
          unmatched90 = false;
          {
            r = ((_1694_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1691_left);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_SeqProperPrefix) {
          unmatched90 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1691_left, _1694_right, _1685_format);
        }
      }
      if (unmatched90) {
        if (_source90.is_SeqPrefix) {
          unmatched90 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1691_left, _1694_right, _1685_format);
        }
      }
      if (unmatched90) {
        if (_source90.is_SetMerge) {
          unmatched90 = false;
          {
            r = ((_1691_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1694_right);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_SetSubtraction) {
          unmatched90 = false;
          {
            r = ((_1691_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1694_right);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_SetIntersection) {
          unmatched90 = false;
          {
            r = ((_1691_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1694_right);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Subset) {
          unmatched90 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1691_left, _1694_right, _1685_format);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_ProperSubset) {
          unmatched90 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1691_left, _1694_right, _1685_format);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_SetDisjoint) {
          unmatched90 = false;
          {
            r = ((_1691_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1694_right);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_MapMerge) {
          unmatched90 = false;
          {
            r = ((_1691_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1694_right);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_MapSubtraction) {
          unmatched90 = false;
          {
            r = ((_1691_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1694_right);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_MultisetMerge) {
          unmatched90 = false;
          {
            r = ((_1691_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1694_right);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_MultisetSubtraction) {
          unmatched90 = false;
          {
            r = ((_1691_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1694_right);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_MultisetIntersection) {
          unmatched90 = false;
          {
            r = ((_1691_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1694_right);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Submultiset) {
          unmatched90 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1691_left, _1694_right, _1685_format);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_ProperSubmultiset) {
          unmatched90 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1691_left, _1694_right, _1685_format);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_MultisetDisjoint) {
          unmatched90 = false;
          {
            r = ((_1691_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1694_right);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Concat) {
          unmatched90 = false;
          {
            r = ((_1691_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1694_right);
          }
        }
      }
      if (unmatched90) {
        unmatched90 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1682_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1682_op), _1691_left, _1694_right, _1685_format);
          } else {
            DAST._IBinOp _source91 = _1682_op;
            bool unmatched91 = true;
            if (unmatched91) {
              if (_source91.is_Eq) {
                bool _1697_referential = _source91.dtor_referential;
                unmatched91 = false;
                {
                  if (_1697_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1691_left, _1694_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1684_rExpr).is_SeqValue) && ((new BigInteger(((_1684_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1691_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1683_lExpr).is_SeqValue) && ((new BigInteger(((_1683_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1694_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1691_left, _1694_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched91) {
              if (_source91.is_EuclidianDiv) {
                unmatched91 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1691_left, _1694_right));
                }
              }
            }
            if (unmatched91) {
              if (_source91.is_EuclidianMod) {
                unmatched91 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1691_left, _1694_right));
                }
              }
            }
            if (unmatched91) {
              Dafny.ISequence<Dafny.Rune> _1698_op = _source91.dtor_Passthrough_a0;
              unmatched91 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1698_op, _1691_left, _1694_right, _1685_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out228;
      DCOMP._IOwnership _out229;
      (this).FromOwned(r, expectedOwnership, out _out228, out _out229);
      r = _out228;
      resultingOwnership = _out229;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1693_recIdentsL, _1696_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1699_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1700_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1701_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1701_toTpe;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1702_path = _let_tmp_rhs57.dtor_path;
      Dafny.ISequence<DAST._IType> _1703_typeArgs = _let_tmp_rhs57.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs58 = _let_tmp_rhs57.dtor_kind;
      DAST._IType _1704_b = _let_tmp_rhs58.dtor_baseType;
      DAST._INewtypeRange _1705_range = _let_tmp_rhs58.dtor_range;
      bool _1706_erase = _let_tmp_rhs58.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1707___v113 = _let_tmp_rhs57.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1708___v114 = _let_tmp_rhs57.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1709___v115 = _let_tmp_rhs57.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1710_nativeToType;
      _1710_nativeToType = DCOMP.COMP.NewtypeToRustType(_1704_b, _1705_range);
      if (object.Equals(_1700_fromTpe, _1704_b)) {
        RAST._IExpr _1711_recursiveGen;
        DCOMP._IOwnership _1712_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1713_recIdents;
        RAST._IExpr _out230;
        DCOMP._IOwnership _out231;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out232;
        (this).GenExpr(_1699_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out230, out _out231, out _out232);
        _1711_recursiveGen = _out230;
        _1712_recOwned = _out231;
        _1713_recIdents = _out232;
        readIdents = _1713_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source92 = _1710_nativeToType;
        bool unmatched92 = true;
        if (unmatched92) {
          if (_source92.is_Some) {
            RAST._IType _1714_v = _source92.dtor_value;
            unmatched92 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1711_recursiveGen, RAST.Expr.create_ExprFromType(_1714_v)));
            RAST._IExpr _out233;
            DCOMP._IOwnership _out234;
            (this).FromOwned(r, expectedOwnership, out _out233, out _out234);
            r = _out233;
            resultingOwnership = _out234;
          }
        }
        if (unmatched92) {
          unmatched92 = false;
          if (_1706_erase) {
            r = _1711_recursiveGen;
          } else {
            RAST._IType _1715_rhsType;
            RAST._IType _out235;
            _out235 = (this).GenType(_1701_toTpe, DCOMP.GenTypeContext.InBinding());
            _1715_rhsType = _out235;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1715_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1711_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out236;
          DCOMP._IOwnership _out237;
          (this).FromOwnership(r, _1712_recOwned, expectedOwnership, out _out236, out _out237);
          r = _out236;
          resultingOwnership = _out237;
        }
      } else {
        if ((_1710_nativeToType).is_Some) {
          DAST._IType _source93 = _1700_fromTpe;
          bool unmatched93 = true;
          if (unmatched93) {
            if (_source93.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source93.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1716_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1717_range0 = kind1.dtor_range;
                bool _1718_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1719_attributes0 = resolved1.dtor_attributes;
                unmatched93 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1720_nativeFromType;
                  _1720_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1716_b0, _1717_range0);
                  if ((_1720_nativeFromType).is_Some) {
                    RAST._IExpr _1721_recursiveGen;
                    DCOMP._IOwnership _1722_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1723_recIdents;
                    RAST._IExpr _out238;
                    DCOMP._IOwnership _out239;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out240;
                    (this).GenExpr(_1699_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out238, out _out239, out _out240);
                    _1721_recursiveGen = _out238;
                    _1722_recOwned = _out239;
                    _1723_recIdents = _out240;
                    RAST._IExpr _out241;
                    DCOMP._IOwnership _out242;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1721_recursiveGen, (_1710_nativeToType).dtor_value), _1722_recOwned, expectedOwnership, out _out241, out _out242);
                    r = _out241;
                    resultingOwnership = _out242;
                    readIdents = _1723_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched93) {
            unmatched93 = false;
          }
          if (object.Equals(_1700_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1724_recursiveGen;
            DCOMP._IOwnership _1725_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1726_recIdents;
            RAST._IExpr _out243;
            DCOMP._IOwnership _out244;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out245;
            (this).GenExpr(_1699_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out243, out _out244, out _out245);
            _1724_recursiveGen = _out243;
            _1725_recOwned = _out244;
            _1726_recIdents = _out245;
            RAST._IExpr _out246;
            DCOMP._IOwnership _out247;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1724_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1710_nativeToType).dtor_value), _1725_recOwned, expectedOwnership, out _out246, out _out247);
            r = _out246;
            resultingOwnership = _out247;
            readIdents = _1726_recIdents;
            return ;
          }
        }
        RAST._IExpr _out248;
        DCOMP._IOwnership _out249;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1699_expr, _1700_fromTpe, _1704_b), _1704_b, _1701_toTpe), selfIdent, env, expectedOwnership, out _out248, out _out249, out _out250);
        r = _out248;
        resultingOwnership = _out249;
        readIdents = _out250;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs59 = e;
      DAST._IExpression _1727_expr = _let_tmp_rhs59.dtor_value;
      DAST._IType _1728_fromTpe = _let_tmp_rhs59.dtor_from;
      DAST._IType _1729_toTpe = _let_tmp_rhs59.dtor_typ;
      DAST._IType _let_tmp_rhs60 = _1728_fromTpe;
      DAST._IResolvedType _let_tmp_rhs61 = _let_tmp_rhs60.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1730___v121 = _let_tmp_rhs61.dtor_path;
      Dafny.ISequence<DAST._IType> _1731___v122 = _let_tmp_rhs61.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs62 = _let_tmp_rhs61.dtor_kind;
      DAST._IType _1732_b = _let_tmp_rhs62.dtor_baseType;
      DAST._INewtypeRange _1733_range = _let_tmp_rhs62.dtor_range;
      bool _1734_erase = _let_tmp_rhs62.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1735_attributes = _let_tmp_rhs61.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1736___v123 = _let_tmp_rhs61.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1737___v124 = _let_tmp_rhs61.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1738_nativeFromType;
      _1738_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1732_b, _1733_range);
      if (object.Equals(_1732_b, _1729_toTpe)) {
        RAST._IExpr _1739_recursiveGen;
        DCOMP._IOwnership _1740_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1741_recIdents;
        RAST._IExpr _out251;
        DCOMP._IOwnership _out252;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
        (this).GenExpr(_1727_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out251, out _out252, out _out253);
        _1739_recursiveGen = _out251;
        _1740_recOwned = _out252;
        _1741_recIdents = _out253;
        readIdents = _1741_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source94 = _1738_nativeFromType;
        bool unmatched94 = true;
        if (unmatched94) {
          if (_source94.is_Some) {
            RAST._IType _1742_v = _source94.dtor_value;
            unmatched94 = false;
            RAST._IType _1743_toTpeRust;
            RAST._IType _out254;
            _out254 = (this).GenType(_1729_toTpe, DCOMP.GenTypeContext.@default());
            _1743_toTpeRust = _out254;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1743_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1739_recursiveGen));
            RAST._IExpr _out255;
            DCOMP._IOwnership _out256;
            (this).FromOwned(r, expectedOwnership, out _out255, out _out256);
            r = _out255;
            resultingOwnership = _out256;
          }
        }
        if (unmatched94) {
          unmatched94 = false;
          if (_1734_erase) {
            r = _1739_recursiveGen;
          } else {
            r = (_1739_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out257;
          DCOMP._IOwnership _out258;
          (this).FromOwnership(r, _1740_recOwned, expectedOwnership, out _out257, out _out258);
          r = _out257;
          resultingOwnership = _out258;
        }
      } else {
        if ((_1738_nativeFromType).is_Some) {
          if (object.Equals(_1729_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1744_recursiveGen;
            DCOMP._IOwnership _1745_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1746_recIdents;
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out261;
            (this).GenExpr(_1727_expr, selfIdent, env, expectedOwnership, out _out259, out _out260, out _out261);
            _1744_recursiveGen = _out259;
            _1745_recOwned = _out260;
            _1746_recIdents = _out261;
            RAST._IExpr _out262;
            DCOMP._IOwnership _out263;
            (this).FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1744_recursiveGen, (this).DafnyCharUnderlying)), _1745_recOwned, expectedOwnership, out _out262, out _out263);
            r = _out262;
            resultingOwnership = _out263;
            readIdents = _1746_recIdents;
            return ;
          }
        }
        RAST._IExpr _out264;
        DCOMP._IOwnership _out265;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1727_expr, _1728_fromTpe, _1732_b), _1732_b, _1729_toTpe), selfIdent, env, expectedOwnership, out _out264, out _out265, out _out266);
        r = _out264;
        resultingOwnership = _out265;
        readIdents = _out266;
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
        Std.Wrappers._IResult<__T, __E> _1747_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1747_valueOrError0).IsFailure()) {
          return (_1747_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1748_head = (_1747_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1749_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1749_valueOrError1).IsFailure()) {
            return (_1749_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1750_tail = (_1749_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1748_head), _1750_tail));
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
          RAST._IType _1751_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1752_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel((this).upcast)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1751_fromTpeUnderlying, _1752_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1753_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1753_valueOrError0).IsFailure()) {
          return (_1753_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1754_lambda = (_1753_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1754_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).Apply1(_1754_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1755_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim12 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr12 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
          for (int i12 = 0; i12 < dim12; i12++) {
            var _1756_i = (BigInteger) i12;
            arr12[(int)(_1756_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_1756_i), ((fromTpe).dtor_arguments).Select(_1756_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_1756_i), ((toTpe).dtor_arguments).Select(_1756_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr12);
        }))());
        if ((_1755_valueOrError1).IsFailure()) {
          return (_1755_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1757_lambdas = (_1755_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim13 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr13 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
  for (int i13 = 0; i13 < dim13; i13++) {
    var _1758_i = (BigInteger) i13;
    arr13[(int)(_1758_i)] = ((fromTpe).dtor_arguments).Select(_1758_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr13);
}))())).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1757_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1759_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1760_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1761_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1762_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1763_valueOrError2 = (this).UpcastConversionLambda(_1761_newFromType, _1759_newFromTpe, _1762_newToType, _1760_newToTpe, typeParams);
        if ((_1763_valueOrError2).IsFailure()) {
          return (_1763_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1764_coerceArg = (_1763_valueOrError2).Extract();
          RAST._IExpr _1765_collectionType = (RAST.__default.dafny__runtime).MSel(((fromTpe).dtor_baseName).dtor_name);
          RAST._IExpr _1766_baseType = (((((fromTpe).dtor_baseName).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? ((_1765_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((fromTpe).dtor_arguments).Select(BigInteger.Zero), _1759_newFromTpe))) : ((_1765_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1759_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1766_baseType).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1764_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1767_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1767_valueOrError3).IsFailure()) {
          return (_1767_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1768_lambda = (_1767_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1768_lambda));
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
      DAST._IExpression _1769_expr = _let_tmp_rhs63.dtor_value;
      DAST._IType _1770_fromTpe = _let_tmp_rhs63.dtor_from;
      DAST._IType _1771_toTpe = _let_tmp_rhs63.dtor_typ;
      RAST._IType _1772_fromTpeGen;
      RAST._IType _out267;
      _out267 = (this).GenType(_1770_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1772_fromTpeGen = _out267;
      RAST._IType _1773_toTpeGen;
      RAST._IType _out268;
      _out268 = (this).GenType(_1771_toTpe, DCOMP.GenTypeContext.InBinding());
      _1773_toTpeGen = _out268;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1774_upcastConverter;
      _1774_upcastConverter = (this).UpcastConversionLambda(_1770_fromTpe, _1772_fromTpeGen, _1771_toTpe, _1773_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1774_upcastConverter).is_Success) {
        RAST._IExpr _1775_conversionLambda;
        _1775_conversionLambda = (_1774_upcastConverter).dtor_value;
        RAST._IExpr _1776_recursiveGen;
        DCOMP._IOwnership _1777_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1778_recIdents;
        RAST._IExpr _out269;
        DCOMP._IOwnership _out270;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
        (this).GenExpr(_1769_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out269, out _out270, out _out271);
        _1776_recursiveGen = _out269;
        _1777_recOwned = _out270;
        _1778_recIdents = _out271;
        readIdents = _1778_recIdents;
        r = (_1775_conversionLambda).Apply1(_1776_recursiveGen);
        RAST._IExpr _out272;
        DCOMP._IOwnership _out273;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out272, out _out273);
        r = _out272;
        resultingOwnership = _out273;
      } else if ((this).IsDowncastConversion(_1772_fromTpeGen, _1773_toTpeGen)) {
        RAST._IExpr _1779_recursiveGen;
        DCOMP._IOwnership _1780_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1781_recIdents;
        RAST._IExpr _out274;
        DCOMP._IOwnership _out275;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out276;
        (this).GenExpr(_1769_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out274, out _out275, out _out276);
        _1779_recursiveGen = _out274;
        _1780_recOwned = _out275;
        _1781_recIdents = _out276;
        readIdents = _1781_recIdents;
        _1773_toTpeGen = (_1773_toTpeGen).ObjectOrPointerUnderlying();
        r = ((RAST.__default.dafny__runtime).MSel((this).downcast)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1779_recursiveGen, RAST.Expr.create_ExprFromType(_1773_toTpeGen)));
        RAST._IExpr _out277;
        DCOMP._IOwnership _out278;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out277, out _out278);
        r = _out277;
        resultingOwnership = _out278;
      } else {
        RAST._IExpr _1782_recursiveGen;
        DCOMP._IOwnership _1783_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1784_recIdents;
        RAST._IExpr _out279;
        DCOMP._IOwnership _out280;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out281;
        (this).GenExpr(_1769_expr, selfIdent, env, expectedOwnership, out _out279, out _out280, out _out281);
        _1782_recursiveGen = _out279;
        _1783_recOwned = _out280;
        _1784_recIdents = _out281;
        readIdents = _1784_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs64 = _1774_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs65 = _let_tmp_rhs64.dtor_error;
        DAST._IType _1785_fromType = _let_tmp_rhs65.dtor__0;
        RAST._IType _1786_fromTpeGen = _let_tmp_rhs65.dtor__1;
        DAST._IType _1787_toType = _let_tmp_rhs65.dtor__2;
        RAST._IType _1788_toTpeGen = _let_tmp_rhs65.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1789_m = _let_tmp_rhs65.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1790_msg;
        _1790_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1786_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1788_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1790_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1782_recursiveGen)._ToString(DCOMP.__default.IND), _1790_msg));
        RAST._IExpr _out282;
        DCOMP._IOwnership _out283;
        (this).FromOwnership(r, _1783_recOwned, expectedOwnership, out _out282, out _out283);
        r = _out282;
        resultingOwnership = _out283;
      }
    }
    public void GenExprConvert(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs66 = e;
      DAST._IExpression _1791_expr = _let_tmp_rhs66.dtor_value;
      DAST._IType _1792_fromTpe = _let_tmp_rhs66.dtor_from;
      DAST._IType _1793_toTpe = _let_tmp_rhs66.dtor_typ;
      if (object.Equals(_1792_fromTpe, _1793_toTpe)) {
        RAST._IExpr _1794_recursiveGen;
        DCOMP._IOwnership _1795_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1796_recIdents;
        RAST._IExpr _out284;
        DCOMP._IOwnership _out285;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
        (this).GenExpr(_1791_expr, selfIdent, env, expectedOwnership, out _out284, out _out285, out _out286);
        _1794_recursiveGen = _out284;
        _1795_recOwned = _out285;
        _1796_recIdents = _out286;
        r = _1794_recursiveGen;
        RAST._IExpr _out287;
        DCOMP._IOwnership _out288;
        (this).FromOwnership(r, _1795_recOwned, expectedOwnership, out _out287, out _out288);
        r = _out287;
        resultingOwnership = _out288;
        readIdents = _1796_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source95 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1792_fromTpe, _1793_toTpe);
        bool unmatched95 = true;
        if (unmatched95) {
          DAST._IType _10 = _source95.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1797_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1798_range = kind2.dtor_range;
              bool _1799_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1800_attributes = resolved2.dtor_attributes;
              unmatched95 = false;
              {
                RAST._IExpr _out289;
                DCOMP._IOwnership _out290;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out291;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out289, out _out290, out _out291);
                r = _out289;
                resultingOwnership = _out290;
                readIdents = _out291;
              }
            }
          }
        }
        if (unmatched95) {
          DAST._IType _00 = _source95.dtor__0;
          if (_00.is_UserDefined) {
            DAST._IResolvedType resolved3 = _00.dtor_resolved;
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1801_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1802_range = kind3.dtor_range;
              bool _1803_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1804_attributes = resolved3.dtor_attributes;
              unmatched95 = false;
              {
                RAST._IExpr _out292;
                DCOMP._IOwnership _out293;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out292, out _out293, out _out294);
                r = _out292;
                resultingOwnership = _out293;
                readIdents = _out294;
              }
            }
          }
        }
        if (unmatched95) {
          DAST._IType _01 = _source95.dtor__0;
          if (_01.is_Primitive) {
            DAST._IPrimitive _h72 = _01.dtor_Primitive_a0;
            if (_h72.is_Int) {
              DAST._IType _11 = _source95.dtor__1;
              if (_11.is_Primitive) {
                DAST._IPrimitive _h73 = _11.dtor_Primitive_a0;
                if (_h73.is_Real) {
                  unmatched95 = false;
                  {
                    RAST._IExpr _1805_recursiveGen;
                    DCOMP._IOwnership _1806___v135;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1807_recIdents;
                    RAST._IExpr _out295;
                    DCOMP._IOwnership _out296;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out297;
                    (this).GenExpr(_1791_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out295, out _out296, out _out297);
                    _1805_recursiveGen = _out295;
                    _1806___v135 = _out296;
                    _1807_recIdents = _out297;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1805_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out298;
                    DCOMP._IOwnership _out299;
                    (this).FromOwned(r, expectedOwnership, out _out298, out _out299);
                    r = _out298;
                    resultingOwnership = _out299;
                    readIdents = _1807_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched95) {
          DAST._IType _02 = _source95.dtor__0;
          if (_02.is_Primitive) {
            DAST._IPrimitive _h74 = _02.dtor_Primitive_a0;
            if (_h74.is_Real) {
              DAST._IType _12 = _source95.dtor__1;
              if (_12.is_Primitive) {
                DAST._IPrimitive _h75 = _12.dtor_Primitive_a0;
                if (_h75.is_Int) {
                  unmatched95 = false;
                  {
                    RAST._IExpr _1808_recursiveGen;
                    DCOMP._IOwnership _1809___v136;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1810_recIdents;
                    RAST._IExpr _out300;
                    DCOMP._IOwnership _out301;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out302;
                    (this).GenExpr(_1791_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out300, out _out301, out _out302);
                    _1808_recursiveGen = _out300;
                    _1809___v136 = _out301;
                    _1810_recIdents = _out302;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1808_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out303;
                    DCOMP._IOwnership _out304;
                    (this).FromOwned(r, expectedOwnership, out _out303, out _out304);
                    r = _out303;
                    resultingOwnership = _out304;
                    readIdents = _1810_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched95) {
          DAST._IType _03 = _source95.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h76 = _03.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _13 = _source95.dtor__1;
              if (_13.is_Passthrough) {
                unmatched95 = false;
                {
                  RAST._IType _1811_rhsType;
                  RAST._IType _out305;
                  _out305 = (this).GenType(_1793_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1811_rhsType = _out305;
                  RAST._IExpr _1812_recursiveGen;
                  DCOMP._IOwnership _1813___v138;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1814_recIdents;
                  RAST._IExpr _out306;
                  DCOMP._IOwnership _out307;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out308;
                  (this).GenExpr(_1791_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out306, out _out307, out _out308);
                  _1812_recursiveGen = _out306;
                  _1813___v138 = _out307;
                  _1814_recIdents = _out308;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1811_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1812_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out309;
                  DCOMP._IOwnership _out310;
                  (this).FromOwned(r, expectedOwnership, out _out309, out _out310);
                  r = _out309;
                  resultingOwnership = _out310;
                  readIdents = _1814_recIdents;
                }
              }
            }
          }
        }
        if (unmatched95) {
          DAST._IType _04 = _source95.dtor__0;
          if (_04.is_Passthrough) {
            DAST._IType _14 = _source95.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h77 = _14.dtor_Primitive_a0;
              if (_h77.is_Int) {
                unmatched95 = false;
                {
                  RAST._IType _1815_rhsType;
                  RAST._IType _out311;
                  _out311 = (this).GenType(_1792_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1815_rhsType = _out311;
                  RAST._IExpr _1816_recursiveGen;
                  DCOMP._IOwnership _1817___v140;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1818_recIdents;
                  RAST._IExpr _out312;
                  DCOMP._IOwnership _out313;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out314;
                  (this).GenExpr(_1791_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out312, out _out313, out _out314);
                  _1816_recursiveGen = _out312;
                  _1817___v140 = _out313;
                  _1818_recIdents = _out314;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1816_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out315;
                  DCOMP._IOwnership _out316;
                  (this).FromOwned(r, expectedOwnership, out _out315, out _out316);
                  r = _out315;
                  resultingOwnership = _out316;
                  readIdents = _1818_recIdents;
                }
              }
            }
          }
        }
        if (unmatched95) {
          DAST._IType _05 = _source95.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h78 = _05.dtor_Primitive_a0;
            if (_h78.is_Int) {
              DAST._IType _15 = _source95.dtor__1;
              if (_15.is_Primitive) {
                DAST._IPrimitive _h79 = _15.dtor_Primitive_a0;
                if (_h79.is_Char) {
                  unmatched95 = false;
                  {
                    RAST._IType _1819_rhsType;
                    RAST._IType _out317;
                    _out317 = (this).GenType(_1793_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1819_rhsType = _out317;
                    RAST._IExpr _1820_recursiveGen;
                    DCOMP._IOwnership _1821___v141;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1822_recIdents;
                    RAST._IExpr _out318;
                    DCOMP._IOwnership _out319;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
                    (this).GenExpr(_1791_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out318, out _out319, out _out320);
                    _1820_recursiveGen = _out318;
                    _1821___v141 = _out319;
                    _1822_recIdents = _out320;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1820_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out321;
                    DCOMP._IOwnership _out322;
                    (this).FromOwned(r, expectedOwnership, out _out321, out _out322);
                    r = _out321;
                    resultingOwnership = _out322;
                    readIdents = _1822_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched95) {
          DAST._IType _06 = _source95.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h710 = _06.dtor_Primitive_a0;
            if (_h710.is_Char) {
              DAST._IType _16 = _source95.dtor__1;
              if (_16.is_Primitive) {
                DAST._IPrimitive _h711 = _16.dtor_Primitive_a0;
                if (_h711.is_Int) {
                  unmatched95 = false;
                  {
                    RAST._IType _1823_rhsType;
                    RAST._IType _out323;
                    _out323 = (this).GenType(_1792_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1823_rhsType = _out323;
                    RAST._IExpr _1824_recursiveGen;
                    DCOMP._IOwnership _1825___v142;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1826_recIdents;
                    RAST._IExpr _out324;
                    DCOMP._IOwnership _out325;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
                    (this).GenExpr(_1791_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out324, out _out325, out _out326);
                    _1824_recursiveGen = _out324;
                    _1825___v142 = _out325;
                    _1826_recIdents = _out326;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1824_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out327;
                    DCOMP._IOwnership _out328;
                    (this).FromOwned(r, expectedOwnership, out _out327, out _out328);
                    r = _out327;
                    resultingOwnership = _out328;
                    readIdents = _1826_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched95) {
          DAST._IType _07 = _source95.dtor__0;
          if (_07.is_Passthrough) {
            DAST._IType _17 = _source95.dtor__1;
            if (_17.is_Passthrough) {
              unmatched95 = false;
              {
                RAST._IExpr _1827_recursiveGen;
                DCOMP._IOwnership _1828___v145;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1829_recIdents;
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExpr(_1791_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out329, out _out330, out _out331);
                _1827_recursiveGen = _out329;
                _1828___v145 = _out330;
                _1829_recIdents = _out331;
                RAST._IType _1830_toTpeGen;
                RAST._IType _out332;
                _out332 = (this).GenType(_1793_toTpe, DCOMP.GenTypeContext.InBinding());
                _1830_toTpeGen = _out332;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1827_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1830_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out333;
                DCOMP._IOwnership _out334;
                (this).FromOwned(r, expectedOwnership, out _out333, out _out334);
                r = _out333;
                resultingOwnership = _out334;
                readIdents = _1829_recIdents;
              }
            }
          }
        }
        if (unmatched95) {
          unmatched95 = false;
          {
            RAST._IExpr _out335;
            DCOMP._IOwnership _out336;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out337;
            (this).GenExprConvertOther(e, selfIdent, env, expectedOwnership, out _out335, out _out336, out _out337);
            r = _out335;
            resultingOwnership = _out336;
            readIdents = _out337;
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
      Std.Wrappers._IOption<RAST._IType> _1831_tpe;
      _1831_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1832_placeboOpt;
      _1832_placeboOpt = (((_1831_tpe).is_Some) ? (((_1831_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1833_currentlyBorrowed;
      _1833_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1834_noNeedOfClone;
      _1834_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1832_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1833_currentlyBorrowed = false;
        _1834_noNeedOfClone = true;
        _1831_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1832_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_1833_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1831_tpe).is_Some) && (((_1831_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1835_needObjectFromRef;
        _1835_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source96 = (selfIdent).dtor_dafnyType;
          bool unmatched96 = true;
          if (unmatched96) {
            if (_source96.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source96.dtor_resolved;
              DAST._IResolvedTypeBase _1836_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1837_attributes = resolved4.dtor_attributes;
              unmatched96 = false;
              return ((_1836_base).is_Class) || ((_1836_base).is_Trait);
            }
          }
          if (unmatched96) {
            unmatched96 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_1835_needObjectFromRef) {
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1834_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1834_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1833_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1831_tpe).is_Some) && (((_1831_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1838_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1838_attributes).UniqueElements, false, (((_exists_var_1) => {
        DAST._IAttribute _1839_attribute = (DAST._IAttribute)_exists_var_1;
        return ((_1838_attributes).Contains(_1839_attribute)) && ((((_1839_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1839_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      BigInteger _hi38 = new BigInteger((args).Count);
      for (BigInteger _1840_i = BigInteger.Zero; _1840_i < _hi38; _1840_i++) {
        DCOMP._IOwnership _1841_argOwnership;
        _1841_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if (((name).is_CallName) && ((_1840_i) < (new BigInteger((((name).dtor_signature)).Count)))) {
          RAST._IType _1842_tpe;
          RAST._IType _out338;
          _out338 = (this).GenType(((((name).dtor_signature)).Select(_1840_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1842_tpe = _out338;
          if ((_1842_tpe).CanReadWithoutClone()) {
            _1841_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1843_argExpr;
        DCOMP._IOwnership _1844___v152;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1845_argIdents;
        RAST._IExpr _out339;
        DCOMP._IOwnership _out340;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out341;
        (this).GenExpr((args).Select(_1840_i), selfIdent, env, _1841_argOwnership, out _out339, out _out340, out _out341);
        _1843_argExpr = _out339;
        _1844___v152 = _out340;
        _1845_argIdents = _out341;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1843_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1845_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi39 = new BigInteger((typeArgs).Count);
      for (BigInteger _1846_typeI = BigInteger.Zero; _1846_typeI < _hi39; _1846_typeI++) {
        RAST._IType _1847_typeExpr;
        RAST._IType _out342;
        _out342 = (this).GenType((typeArgs).Select(_1846_typeI), DCOMP.GenTypeContext.@default());
        _1847_typeExpr = _out342;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1847_typeExpr));
      }
      DAST._ICallName _source97 = name;
      bool unmatched97 = true;
      if (unmatched97) {
        if (_source97.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _1848_nameIdent = _source97.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType1 = _source97.dtor_onType;
          if (onType1.is_Some) {
            DAST._IType value10 = onType1.dtor_value;
            if (value10.is_UserDefined) {
              DAST._IResolvedType _1849_resolvedType = value10.dtor_resolved;
              unmatched97 = false;
              if ((((_1849_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_1850_resolvedType, _1851_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(((_1850_resolvedType).dtor_properMethods).UniqueElements, true, (((_forall_var_8) => {
                Dafny.ISequence<Dafny.Rune> _1852_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                return !(((_1850_resolvedType).dtor_properMethods).Contains(_1852_m)) || (!object.Equals((_1852_m), _1851_nameIdent));
              }))))(_1849_resolvedType, _1848_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_1849_resolvedType, (_1848_nameIdent)), _1849_resolvedType));
              } else {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
              }
            }
          }
        }
      }
      if (unmatched97) {
        unmatched97 = false;
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
      if ((((((fullNameQualifier).is_Some) && ((selfIdent).is_ThisTyped)) && (((selfIdent).dtor_dafnyType).is_UserDefined)) && ((this).IsSameResolvedType(((selfIdent).dtor_dafnyType).dtor_resolved, (fullNameQualifier).dtor_value))) && (!((this).HasExternAttributeRenamingModule(((fullNameQualifier).dtor_value).dtor_attributes)))) {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    }
    public Dafny.ISequence<Dafny.Rune> GetMethodName(DAST._IExpression @on, DAST._ICallName name)
    {
      var _pat_let_tv143 = @on;
      DAST._ICallName _source98 = name;
      bool unmatched98 = true;
      if (unmatched98) {
        if (_source98.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _1853_ident = _source98.dtor_name;
          unmatched98 = false;
          if ((_pat_let_tv143).is_ExternCompanion) {
            return (_1853_ident);
          } else {
            return DCOMP.__default.escapeName(_1853_ident);
          }
        }
      }
      if (unmatched98) {
        bool disjunctiveMatch14 = false;
        if (_source98.is_MapBuilderAdd) {
          disjunctiveMatch14 = true;
        }
        if (_source98.is_SetBuilderAdd) {
          disjunctiveMatch14 = true;
        }
        if (disjunctiveMatch14) {
          unmatched98 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
        }
      }
      if (unmatched98) {
        bool disjunctiveMatch15 = false;
        disjunctiveMatch15 = true;
        disjunctiveMatch15 = true;
        if (disjunctiveMatch15) {
          unmatched98 = false;
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
      DAST._IExpression _source99 = e;
      bool unmatched99 = true;
      if (unmatched99) {
        if (_source99.is_Literal) {
          unmatched99 = false;
          RAST._IExpr _out343;
          DCOMP._IOwnership _out344;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out345;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out343, out _out344, out _out345);
          r = _out343;
          resultingOwnership = _out344;
          readIdents = _out345;
        }
      }
      if (unmatched99) {
        if (_source99.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1854_name = _source99.dtor_name;
          unmatched99 = false;
          {
            RAST._IExpr _out346;
            DCOMP._IOwnership _out347;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
            (this).GenIdent(DCOMP.__default.escapeName(_1854_name), selfIdent, env, expectedOwnership, out _out346, out _out347, out _out348);
            r = _out346;
            resultingOwnership = _out347;
            readIdents = _out348;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_ExternCompanion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1855_path = _source99.dtor_ExternCompanion_a0;
          unmatched99 = false;
          {
            RAST._IExpr _out349;
            _out349 = DCOMP.COMP.GenPathExpr(_1855_path, false);
            r = _out349;
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out350;
              DCOMP._IOwnership _out351;
              (this).FromOwned(r, expectedOwnership, out _out350, out _out351);
              r = _out350;
              resultingOwnership = _out351;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1856_path = _source99.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _1857_typeArgs = _source99.dtor_typeArgs;
          unmatched99 = false;
          {
            RAST._IExpr _out352;
            _out352 = DCOMP.COMP.GenPathExpr(_1856_path, true);
            r = _out352;
            if ((new BigInteger((_1857_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1858_typeExprs;
              _1858_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_1857_typeArgs).Count);
              for (BigInteger _1859_i = BigInteger.Zero; _1859_i < _hi40; _1859_i++) {
                RAST._IType _1860_typeExpr;
                RAST._IType _out353;
                _out353 = (this).GenType((_1857_typeArgs).Select(_1859_i), DCOMP.GenTypeContext.@default());
                _1860_typeExpr = _out353;
                _1858_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1858_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1860_typeExpr));
              }
              r = (r).ApplyType(_1858_typeExprs);
            }
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out354;
              DCOMP._IOwnership _out355;
              (this).FromOwned(r, expectedOwnership, out _out354, out _out355);
              r = _out354;
              resultingOwnership = _out355;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_InitializationValue) {
          DAST._IType _1861_typ = _source99.dtor_typ;
          unmatched99 = false;
          {
            RAST._IType _1862_typExpr;
            RAST._IType _out356;
            _out356 = (this).GenType(_1861_typ, DCOMP.GenTypeContext.@default());
            _1862_typExpr = _out356;
            if ((_1862_typExpr).IsObjectOrPointer()) {
              r = (_1862_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1862_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            }
            RAST._IExpr _out357;
            DCOMP._IOwnership _out358;
            (this).FromOwned(r, expectedOwnership, out _out357, out _out358);
            r = _out357;
            resultingOwnership = _out358;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1863_values = _source99.dtor_Tuple_a0;
          unmatched99 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1864_exprs;
            _1864_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi41 = new BigInteger((_1863_values).Count);
            for (BigInteger _1865_i = BigInteger.Zero; _1865_i < _hi41; _1865_i++) {
              RAST._IExpr _1866_recursiveGen;
              DCOMP._IOwnership _1867___v160;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1868_recIdents;
              RAST._IExpr _out359;
              DCOMP._IOwnership _out360;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out361;
              (this).GenExpr((_1863_values).Select(_1865_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out359, out _out360, out _out361);
              _1866_recursiveGen = _out359;
              _1867___v160 = _out360;
              _1868_recIdents = _out361;
              _1864_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1864_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1866_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1868_recIdents);
            }
            r = (((new BigInteger((_1863_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1864_exprs)) : (RAST.__default.SystemTuple(_1864_exprs)));
            RAST._IExpr _out362;
            DCOMP._IOwnership _out363;
            (this).FromOwned(r, expectedOwnership, out _out362, out _out363);
            r = _out362;
            resultingOwnership = _out363;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1869_path = _source99.dtor_path;
          Dafny.ISequence<DAST._IType> _1870_typeArgs = _source99.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1871_args = _source99.dtor_args;
          unmatched99 = false;
          {
            RAST._IExpr _out364;
            _out364 = DCOMP.COMP.GenPathExpr(_1869_path, true);
            r = _out364;
            if ((new BigInteger((_1870_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1872_typeExprs;
              _1872_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi42 = new BigInteger((_1870_typeArgs).Count);
              for (BigInteger _1873_i = BigInteger.Zero; _1873_i < _hi42; _1873_i++) {
                RAST._IType _1874_typeExpr;
                RAST._IType _out365;
                _out365 = (this).GenType((_1870_typeArgs).Select(_1873_i), DCOMP.GenTypeContext.@default());
                _1874_typeExpr = _out365;
                _1872_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1872_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1874_typeExpr));
              }
              r = (r).ApplyType(_1872_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1875_arguments;
            _1875_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi43 = new BigInteger((_1871_args).Count);
            for (BigInteger _1876_i = BigInteger.Zero; _1876_i < _hi43; _1876_i++) {
              RAST._IExpr _1877_recursiveGen;
              DCOMP._IOwnership _1878___v161;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1879_recIdents;
              RAST._IExpr _out366;
              DCOMP._IOwnership _out367;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out368;
              (this).GenExpr((_1871_args).Select(_1876_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out366, out _out367, out _out368);
              _1877_recursiveGen = _out366;
              _1878___v161 = _out367;
              _1879_recIdents = _out368;
              _1875_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1875_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1877_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1879_recIdents);
            }
            r = (r).Apply(_1875_arguments);
            RAST._IExpr _out369;
            DCOMP._IOwnership _out370;
            (this).FromOwned(r, expectedOwnership, out _out369, out _out370);
            r = _out369;
            resultingOwnership = _out370;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _1880_dims = _source99.dtor_dims;
          DAST._IType _1881_typ = _source99.dtor_typ;
          unmatched99 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1880_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1882_msg;
              _1882_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1882_msg);
              }
              r = RAST.Expr.create_RawExpr(_1882_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1883_typeGen;
              RAST._IType _out371;
              _out371 = (this).GenType(_1881_typ, DCOMP.GenTypeContext.@default());
              _1883_typeGen = _out371;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1884_dimExprs;
              _1884_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi44 = new BigInteger((_1880_dims).Count);
              for (BigInteger _1885_i = BigInteger.Zero; _1885_i < _hi44; _1885_i++) {
                RAST._IExpr _1886_recursiveGen;
                DCOMP._IOwnership _1887___v162;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1888_recIdents;
                RAST._IExpr _out372;
                DCOMP._IOwnership _out373;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out374;
                (this).GenExpr((_1880_dims).Select(_1885_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out372, out _out373, out _out374);
                _1886_recursiveGen = _out372;
                _1887___v162 = _out373;
                _1888_recIdents = _out374;
                _1884_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1884_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_1886_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1888_recIdents);
              }
              if ((new BigInteger((_1880_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1889_class__name;
                _1889_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1880_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1889_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1883_typeGen))).MSel((this).placebos__usize)).Apply(_1884_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1883_typeGen))).Apply(_1884_dimExprs);
              }
            }
            RAST._IExpr _out375;
            DCOMP._IOwnership _out376;
            (this).FromOwned(r, expectedOwnership, out _out375, out _out376);
            r = _out375;
            resultingOwnership = _out376;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_ArrayIndexToInt) {
          DAST._IExpression _1890_underlying = _source99.dtor_value;
          unmatched99 = false;
          {
            RAST._IExpr _1891_recursiveGen;
            DCOMP._IOwnership _1892___v163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1893_recIdents;
            RAST._IExpr _out377;
            DCOMP._IOwnership _out378;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out379;
            (this).GenExpr(_1890_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out377, out _out378, out _out379);
            _1891_recursiveGen = _out377;
            _1892___v163 = _out378;
            _1893_recIdents = _out379;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1891_recursiveGen);
            readIdents = _1893_recIdents;
            RAST._IExpr _out380;
            DCOMP._IOwnership _out381;
            (this).FromOwned(r, expectedOwnership, out _out380, out _out381);
            r = _out380;
            resultingOwnership = _out381;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_FinalizeNewArray) {
          DAST._IExpression _1894_underlying = _source99.dtor_value;
          DAST._IType _1895_typ = _source99.dtor_typ;
          unmatched99 = false;
          {
            RAST._IType _1896_tpe;
            RAST._IType _out382;
            _out382 = (this).GenType(_1895_typ, DCOMP.GenTypeContext.@default());
            _1896_tpe = _out382;
            RAST._IExpr _1897_recursiveGen;
            DCOMP._IOwnership _1898___v164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1899_recIdents;
            RAST._IExpr _out383;
            DCOMP._IOwnership _out384;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out385;
            (this).GenExpr(_1894_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out383, out _out384, out _out385);
            _1897_recursiveGen = _out383;
            _1898___v164 = _out384;
            _1899_recIdents = _out385;
            readIdents = _1899_recIdents;
            if ((_1896_tpe).IsObjectOrPointer()) {
              RAST._IType _1900_t;
              _1900_t = (_1896_tpe).ObjectOrPointerUnderlying();
              if ((_1900_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1897_recursiveGen);
              } else if ((_1900_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1901_c;
                _1901_c = (_1900_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1901_c)).MSel((this).array__construct)).Apply1(_1897_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1896_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1896_tpe)._ToString(DCOMP.__default.IND)));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            }
            RAST._IExpr _out386;
            DCOMP._IOwnership _out387;
            (this).FromOwned(r, expectedOwnership, out _out386, out _out387);
            r = _out386;
            resultingOwnership = _out387;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_DatatypeValue) {
          DAST._IResolvedType _1902_datatypeType = _source99.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1903_typeArgs = _source99.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1904_variant = _source99.dtor_variant;
          bool _1905_isCo = _source99.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1906_values = _source99.dtor_contents;
          unmatched99 = false;
          {
            RAST._IExpr _out388;
            _out388 = DCOMP.COMP.GenPathExpr((_1902_datatypeType).dtor_path, true);
            r = _out388;
            Dafny.ISequence<RAST._IType> _1907_genTypeArgs;
            _1907_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi45 = new BigInteger((_1903_typeArgs).Count);
            for (BigInteger _1908_i = BigInteger.Zero; _1908_i < _hi45; _1908_i++) {
              RAST._IType _1909_typeExpr;
              RAST._IType _out389;
              _out389 = (this).GenType((_1903_typeArgs).Select(_1908_i), DCOMP.GenTypeContext.@default());
              _1909_typeExpr = _out389;
              _1907_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1907_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1909_typeExpr));
            }
            if ((new BigInteger((_1903_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1907_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1904_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1910_assignments;
            _1910_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi46 = new BigInteger((_1906_values).Count);
            for (BigInteger _1911_i = BigInteger.Zero; _1911_i < _hi46; _1911_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs67 = (_1906_values).Select(_1911_i);
              Dafny.ISequence<Dafny.Rune> _1912_name = _let_tmp_rhs67.dtor__0;
              DAST._IExpression _1913_value = _let_tmp_rhs67.dtor__1;
              if (_1905_isCo) {
                RAST._IExpr _1914_recursiveGen;
                DCOMP._IOwnership _1915___v165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1916_recIdents;
                RAST._IExpr _out390;
                DCOMP._IOwnership _out391;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out392;
                (this).GenExpr(_1913_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out390, out _out391, out _out392);
                _1914_recursiveGen = _out390;
                _1915___v165 = _out391;
                _1916_recIdents = _out392;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1916_recIdents);
                Dafny.ISequence<Dafny.Rune> _1917_allReadCloned;
                _1917_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1916_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1918_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1916_recIdents).Elements) {
                    _1918_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1916_recIdents).Contains(_1918_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4534)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1917_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1917_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1918_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1918_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1916_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1916_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1918_next));
                }
                Dafny.ISequence<Dafny.Rune> _1919_wasAssigned;
                _1919_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1917_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1914_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1910_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1910_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1912_name), RAST.Expr.create_RawExpr(_1919_wasAssigned))));
              } else {
                RAST._IExpr _1920_recursiveGen;
                DCOMP._IOwnership _1921___v166;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1922_recIdents;
                RAST._IExpr _out393;
                DCOMP._IOwnership _out394;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
                (this).GenExpr(_1913_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out393, out _out394, out _out395);
                _1920_recursiveGen = _out393;
                _1921___v166 = _out394;
                _1922_recIdents = _out395;
                _1910_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1910_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1912_name), _1920_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1922_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1910_assignments);
            if ((this).IsRcWrapped((_1902_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out396;
            DCOMP._IOwnership _out397;
            (this).FromOwned(r, expectedOwnership, out _out396, out _out397);
            r = _out396;
            resultingOwnership = _out397;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_Convert) {
          unmatched99 = false;
          {
            RAST._IExpr _out398;
            DCOMP._IOwnership _out399;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out398, out _out399, out _out400);
            r = _out398;
            resultingOwnership = _out399;
            readIdents = _out400;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_SeqConstruct) {
          DAST._IExpression _1923_length = _source99.dtor_length;
          DAST._IExpression _1924_expr = _source99.dtor_elem;
          unmatched99 = false;
          {
            RAST._IExpr _1925_recursiveGen;
            DCOMP._IOwnership _1926___v170;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1927_recIdents;
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
            (this).GenExpr(_1924_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out401, out _out402, out _out403);
            _1925_recursiveGen = _out401;
            _1926___v170 = _out402;
            _1927_recIdents = _out403;
            RAST._IExpr _1928_lengthGen;
            DCOMP._IOwnership _1929___v171;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1930_lengthIdents;
            RAST._IExpr _out404;
            DCOMP._IOwnership _out405;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out406;
            (this).GenExpr(_1923_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out404, out _out405, out _out406);
            _1928_lengthGen = _out404;
            _1929___v171 = _out405;
            _1930_lengthIdents = _out406;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1925_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1928_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1927_recIdents, _1930_lengthIdents);
            RAST._IExpr _out407;
            DCOMP._IOwnership _out408;
            (this).FromOwned(r, expectedOwnership, out _out407, out _out408);
            r = _out407;
            resultingOwnership = _out408;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1931_exprs = _source99.dtor_elements;
          DAST._IType _1932_typ = _source99.dtor_typ;
          unmatched99 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1933_genTpe;
            RAST._IType _out409;
            _out409 = (this).GenType(_1932_typ, DCOMP.GenTypeContext.@default());
            _1933_genTpe = _out409;
            BigInteger _1934_i;
            _1934_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1935_args;
            _1935_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1934_i) < (new BigInteger((_1931_exprs).Count))) {
              RAST._IExpr _1936_recursiveGen;
              DCOMP._IOwnership _1937___v172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1938_recIdents;
              RAST._IExpr _out410;
              DCOMP._IOwnership _out411;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out412;
              (this).GenExpr((_1931_exprs).Select(_1934_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out410, out _out411, out _out412);
              _1936_recursiveGen = _out410;
              _1937___v172 = _out411;
              _1938_recIdents = _out412;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1938_recIdents);
              _1935_args = Dafny.Sequence<RAST._IExpr>.Concat(_1935_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1936_recursiveGen));
              _1934_i = (_1934_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1935_args);
            if ((new BigInteger((_1935_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1933_genTpe));
            }
            RAST._IExpr _out413;
            DCOMP._IOwnership _out414;
            (this).FromOwned(r, expectedOwnership, out _out413, out _out414);
            r = _out413;
            resultingOwnership = _out414;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1939_exprs = _source99.dtor_elements;
          unmatched99 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1940_generatedValues;
            _1940_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1941_i;
            _1941_i = BigInteger.Zero;
            while ((_1941_i) < (new BigInteger((_1939_exprs).Count))) {
              RAST._IExpr _1942_recursiveGen;
              DCOMP._IOwnership _1943___v173;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1944_recIdents;
              RAST._IExpr _out415;
              DCOMP._IOwnership _out416;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out417;
              (this).GenExpr((_1939_exprs).Select(_1941_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out415, out _out416, out _out417);
              _1942_recursiveGen = _out415;
              _1943___v173 = _out416;
              _1944_recIdents = _out417;
              _1940_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1940_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1942_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1944_recIdents);
              _1941_i = (_1941_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1940_generatedValues);
            RAST._IExpr _out418;
            DCOMP._IOwnership _out419;
            (this).FromOwned(r, expectedOwnership, out _out418, out _out419);
            r = _out418;
            resultingOwnership = _out419;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1945_exprs = _source99.dtor_elements;
          unmatched99 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1946_generatedValues;
            _1946_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1947_i;
            _1947_i = BigInteger.Zero;
            while ((_1947_i) < (new BigInteger((_1945_exprs).Count))) {
              RAST._IExpr _1948_recursiveGen;
              DCOMP._IOwnership _1949___v174;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1950_recIdents;
              RAST._IExpr _out420;
              DCOMP._IOwnership _out421;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out422;
              (this).GenExpr((_1945_exprs).Select(_1947_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out420, out _out421, out _out422);
              _1948_recursiveGen = _out420;
              _1949___v174 = _out421;
              _1950_recIdents = _out422;
              _1946_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1946_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1948_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1950_recIdents);
              _1947_i = (_1947_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1946_generatedValues);
            RAST._IExpr _out423;
            DCOMP._IOwnership _out424;
            (this).FromOwned(r, expectedOwnership, out _out423, out _out424);
            r = _out423;
            resultingOwnership = _out424;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_ToMultiset) {
          DAST._IExpression _1951_expr = _source99.dtor_ToMultiset_a0;
          unmatched99 = false;
          {
            RAST._IExpr _1952_recursiveGen;
            DCOMP._IOwnership _1953___v175;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1954_recIdents;
            RAST._IExpr _out425;
            DCOMP._IOwnership _out426;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out427;
            (this).GenExpr(_1951_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out425, out _out426, out _out427);
            _1952_recursiveGen = _out425;
            _1953___v175 = _out426;
            _1954_recIdents = _out427;
            r = ((_1952_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1954_recIdents;
            RAST._IExpr _out428;
            DCOMP._IOwnership _out429;
            (this).FromOwned(r, expectedOwnership, out _out428, out _out429);
            r = _out428;
            resultingOwnership = _out429;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1955_mapElems = _source99.dtor_mapElems;
          unmatched99 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1956_generatedValues;
            _1956_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1957_i;
            _1957_i = BigInteger.Zero;
            while ((_1957_i) < (new BigInteger((_1955_mapElems).Count))) {
              RAST._IExpr _1958_recursiveGenKey;
              DCOMP._IOwnership _1959___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1960_recIdentsKey;
              RAST._IExpr _out430;
              DCOMP._IOwnership _out431;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out432;
              (this).GenExpr(((_1955_mapElems).Select(_1957_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out430, out _out431, out _out432);
              _1958_recursiveGenKey = _out430;
              _1959___v176 = _out431;
              _1960_recIdentsKey = _out432;
              RAST._IExpr _1961_recursiveGenValue;
              DCOMP._IOwnership _1962___v177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1963_recIdentsValue;
              RAST._IExpr _out433;
              DCOMP._IOwnership _out434;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out435;
              (this).GenExpr(((_1955_mapElems).Select(_1957_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out433, out _out434, out _out435);
              _1961_recursiveGenValue = _out433;
              _1962___v177 = _out434;
              _1963_recIdentsValue = _out435;
              _1956_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1956_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1958_recursiveGenKey, _1961_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1960_recIdentsKey), _1963_recIdentsValue);
              _1957_i = (_1957_i) + (BigInteger.One);
            }
            _1957_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1964_arguments;
            _1964_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1957_i) < (new BigInteger((_1956_generatedValues).Count))) {
              RAST._IExpr _1965_genKey;
              _1965_genKey = ((_1956_generatedValues).Select(_1957_i)).dtor__0;
              RAST._IExpr _1966_genValue;
              _1966_genValue = ((_1956_generatedValues).Select(_1957_i)).dtor__1;
              _1964_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1964_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1965_genKey, _1966_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1957_i = (_1957_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1964_arguments);
            RAST._IExpr _out436;
            DCOMP._IOwnership _out437;
            (this).FromOwned(r, expectedOwnership, out _out436, out _out437);
            r = _out436;
            resultingOwnership = _out437;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_SeqUpdate) {
          DAST._IExpression _1967_expr = _source99.dtor_expr;
          DAST._IExpression _1968_index = _source99.dtor_indexExpr;
          DAST._IExpression _1969_value = _source99.dtor_value;
          unmatched99 = false;
          {
            RAST._IExpr _1970_exprR;
            DCOMP._IOwnership _1971___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1972_exprIdents;
            RAST._IExpr _out438;
            DCOMP._IOwnership _out439;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
            (this).GenExpr(_1967_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out438, out _out439, out _out440);
            _1970_exprR = _out438;
            _1971___v178 = _out439;
            _1972_exprIdents = _out440;
            RAST._IExpr _1973_indexR;
            DCOMP._IOwnership _1974_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1975_indexIdents;
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
            (this).GenExpr(_1968_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out441, out _out442, out _out443);
            _1973_indexR = _out441;
            _1974_indexOwnership = _out442;
            _1975_indexIdents = _out443;
            RAST._IExpr _1976_valueR;
            DCOMP._IOwnership _1977_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1978_valueIdents;
            RAST._IExpr _out444;
            DCOMP._IOwnership _out445;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out446;
            (this).GenExpr(_1969_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out444, out _out445, out _out446);
            _1976_valueR = _out444;
            _1977_valueOwnership = _out445;
            _1978_valueIdents = _out446;
            r = ((_1970_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1973_indexR, _1976_valueR));
            RAST._IExpr _out447;
            DCOMP._IOwnership _out448;
            (this).FromOwned(r, expectedOwnership, out _out447, out _out448);
            r = _out447;
            resultingOwnership = _out448;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1972_exprIdents, _1975_indexIdents), _1978_valueIdents);
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_MapUpdate) {
          DAST._IExpression _1979_expr = _source99.dtor_expr;
          DAST._IExpression _1980_index = _source99.dtor_indexExpr;
          DAST._IExpression _1981_value = _source99.dtor_value;
          unmatched99 = false;
          {
            RAST._IExpr _1982_exprR;
            DCOMP._IOwnership _1983___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1984_exprIdents;
            RAST._IExpr _out449;
            DCOMP._IOwnership _out450;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
            (this).GenExpr(_1979_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out449, out _out450, out _out451);
            _1982_exprR = _out449;
            _1983___v179 = _out450;
            _1984_exprIdents = _out451;
            RAST._IExpr _1985_indexR;
            DCOMP._IOwnership _1986_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1987_indexIdents;
            RAST._IExpr _out452;
            DCOMP._IOwnership _out453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
            (this).GenExpr(_1980_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out452, out _out453, out _out454);
            _1985_indexR = _out452;
            _1986_indexOwnership = _out453;
            _1987_indexIdents = _out454;
            RAST._IExpr _1988_valueR;
            DCOMP._IOwnership _1989_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1990_valueIdents;
            RAST._IExpr _out455;
            DCOMP._IOwnership _out456;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out457;
            (this).GenExpr(_1981_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out455, out _out456, out _out457);
            _1988_valueR = _out455;
            _1989_valueOwnership = _out456;
            _1990_valueIdents = _out457;
            r = ((_1982_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1985_indexR, _1988_valueR));
            RAST._IExpr _out458;
            DCOMP._IOwnership _out459;
            (this).FromOwned(r, expectedOwnership, out _out458, out _out459);
            r = _out458;
            resultingOwnership = _out459;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1984_exprIdents, _1987_indexIdents), _1990_valueIdents);
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_This) {
          unmatched99 = false;
          {
            DCOMP._ISelfInfo _source100 = selfIdent;
            bool unmatched100 = true;
            if (unmatched100) {
              if (_source100.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _1991_id = _source100.dtor_rSelfName;
                DAST._IType _1992_dafnyType = _source100.dtor_dafnyType;
                unmatched100 = false;
                {
                  RAST._IExpr _out460;
                  DCOMP._IOwnership _out461;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out462;
                  (this).GenIdent(_1991_id, selfIdent, env, expectedOwnership, out _out460, out _out461, out _out462);
                  r = _out460;
                  resultingOwnership = _out461;
                  readIdents = _out462;
                }
              }
            }
            if (unmatched100) {
              DCOMP._ISelfInfo _1993_None = _source100;
              unmatched100 = false;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out463;
                DCOMP._IOwnership _out464;
                (this).FromOwned(r, expectedOwnership, out _out463, out _out464);
                r = _out463;
                resultingOwnership = _out464;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_Ite) {
          DAST._IExpression _1994_cond = _source99.dtor_cond;
          DAST._IExpression _1995_t = _source99.dtor_thn;
          DAST._IExpression _1996_f = _source99.dtor_els;
          unmatched99 = false;
          {
            RAST._IExpr _1997_cond;
            DCOMP._IOwnership _1998___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1999_recIdentsCond;
            RAST._IExpr _out465;
            DCOMP._IOwnership _out466;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out467;
            (this).GenExpr(_1994_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out465, out _out466, out _out467);
            _1997_cond = _out465;
            _1998___v180 = _out466;
            _1999_recIdentsCond = _out467;
            RAST._IExpr _2000_fExpr;
            DCOMP._IOwnership _2001_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2002_recIdentsF;
            RAST._IExpr _out468;
            DCOMP._IOwnership _out469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out470;
            (this).GenExpr(_1996_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out468, out _out469, out _out470);
            _2000_fExpr = _out468;
            _2001_fOwned = _out469;
            _2002_recIdentsF = _out470;
            RAST._IExpr _2003_tExpr;
            DCOMP._IOwnership _2004___v181;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2005_recIdentsT;
            RAST._IExpr _out471;
            DCOMP._IOwnership _out472;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out473;
            (this).GenExpr(_1995_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out471, out _out472, out _out473);
            _2003_tExpr = _out471;
            _2004___v181 = _out472;
            _2005_recIdentsT = _out473;
            r = RAST.Expr.create_IfExpr(_1997_cond, _2003_tExpr, _2000_fExpr);
            RAST._IExpr _out474;
            DCOMP._IOwnership _out475;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out474, out _out475);
            r = _out474;
            resultingOwnership = _out475;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1999_recIdentsCond, _2005_recIdentsT), _2002_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source99.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _2006_e = _source99.dtor_expr;
            DAST.Format._IUnaryOpFormat _2007_format = _source99.dtor_format1;
            unmatched99 = false;
            {
              RAST._IExpr _2008_recursiveGen;
              DCOMP._IOwnership _2009___v182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2010_recIdents;
              RAST._IExpr _out476;
              DCOMP._IOwnership _out477;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out478;
              (this).GenExpr(_2006_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out476, out _out477, out _out478);
              _2008_recursiveGen = _out476;
              _2009___v182 = _out477;
              _2010_recIdents = _out478;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _2008_recursiveGen, _2007_format);
              RAST._IExpr _out479;
              DCOMP._IOwnership _out480;
              (this).FromOwned(r, expectedOwnership, out _out479, out _out480);
              r = _out479;
              resultingOwnership = _out480;
              readIdents = _2010_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source99.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _2011_e = _source99.dtor_expr;
            DAST.Format._IUnaryOpFormat _2012_format = _source99.dtor_format1;
            unmatched99 = false;
            {
              RAST._IExpr _2013_recursiveGen;
              DCOMP._IOwnership _2014___v183;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2015_recIdents;
              RAST._IExpr _out481;
              DCOMP._IOwnership _out482;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out483;
              (this).GenExpr(_2011_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out481, out _out482, out _out483);
              _2013_recursiveGen = _out481;
              _2014___v183 = _out482;
              _2015_recIdents = _out483;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _2013_recursiveGen, _2012_format);
              RAST._IExpr _out484;
              DCOMP._IOwnership _out485;
              (this).FromOwned(r, expectedOwnership, out _out484, out _out485);
              r = _out484;
              resultingOwnership = _out485;
              readIdents = _2015_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source99.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _2016_e = _source99.dtor_expr;
            DAST.Format._IUnaryOpFormat _2017_format = _source99.dtor_format1;
            unmatched99 = false;
            {
              RAST._IExpr _2018_recursiveGen;
              DCOMP._IOwnership _2019_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2020_recIdents;
              RAST._IExpr _out486;
              DCOMP._IOwnership _out487;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out488;
              (this).GenExpr(_2016_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out486, out _out487, out _out488);
              _2018_recursiveGen = _out486;
              _2019_recOwned = _out487;
              _2020_recIdents = _out488;
              r = ((_2018_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out489;
              DCOMP._IOwnership _out490;
              (this).FromOwned(r, expectedOwnership, out _out489, out _out490);
              r = _out489;
              resultingOwnership = _out490;
              readIdents = _2020_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_BinOp) {
          unmatched99 = false;
          RAST._IExpr _out491;
          DCOMP._IOwnership _out492;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out491, out _out492, out _out493);
          r = _out491;
          resultingOwnership = _out492;
          readIdents = _out493;
        }
      }
      if (unmatched99) {
        if (_source99.is_ArrayLen) {
          DAST._IExpression _2021_expr = _source99.dtor_expr;
          DAST._IType _2022_exprType = _source99.dtor_exprType;
          BigInteger _2023_dim = _source99.dtor_dim;
          bool _2024_native = _source99.dtor_native;
          unmatched99 = false;
          {
            RAST._IExpr _2025_recursiveGen;
            DCOMP._IOwnership _2026___v188;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2027_recIdents;
            RAST._IExpr _out494;
            DCOMP._IOwnership _out495;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
            (this).GenExpr(_2021_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out494, out _out495, out _out496);
            _2025_recursiveGen = _out494;
            _2026___v188 = _out495;
            _2027_recIdents = _out496;
            RAST._IType _2028_arrayType;
            RAST._IType _out497;
            _out497 = (this).GenType(_2022_exprType, DCOMP.GenTypeContext.@default());
            _2028_arrayType = _out497;
            if (!((_2028_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2029_msg;
              _2029_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2028_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2029_msg);
              r = RAST.Expr.create_RawExpr(_2029_msg);
            } else {
              RAST._IType _2030_underlying;
              _2030_underlying = (_2028_arrayType).ObjectOrPointerUnderlying();
              if (((_2023_dim).Sign == 0) && ((_2030_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2025_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2023_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2025_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_2025_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_2023_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_2024_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out498;
            DCOMP._IOwnership _out499;
            (this).FromOwned(r, expectedOwnership, out _out498, out _out499);
            r = _out498;
            resultingOwnership = _out499;
            readIdents = _2027_recIdents;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_MapKeys) {
          DAST._IExpression _2031_expr = _source99.dtor_expr;
          unmatched99 = false;
          {
            RAST._IExpr _2032_recursiveGen;
            DCOMP._IOwnership _2033___v189;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2034_recIdents;
            RAST._IExpr _out500;
            DCOMP._IOwnership _out501;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out502;
            (this).GenExpr(_2031_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out500, out _out501, out _out502);
            _2032_recursiveGen = _out500;
            _2033___v189 = _out501;
            _2034_recIdents = _out502;
            readIdents = _2034_recIdents;
            r = ((_2032_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out503;
            DCOMP._IOwnership _out504;
            (this).FromOwned(r, expectedOwnership, out _out503, out _out504);
            r = _out503;
            resultingOwnership = _out504;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_MapValues) {
          DAST._IExpression _2035_expr = _source99.dtor_expr;
          unmatched99 = false;
          {
            RAST._IExpr _2036_recursiveGen;
            DCOMP._IOwnership _2037___v190;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2038_recIdents;
            RAST._IExpr _out505;
            DCOMP._IOwnership _out506;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out507;
            (this).GenExpr(_2035_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out505, out _out506, out _out507);
            _2036_recursiveGen = _out505;
            _2037___v190 = _out506;
            _2038_recIdents = _out507;
            readIdents = _2038_recIdents;
            r = ((_2036_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out508;
            DCOMP._IOwnership _out509;
            (this).FromOwned(r, expectedOwnership, out _out508, out _out509);
            r = _out508;
            resultingOwnership = _out509;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_SelectFn) {
          DAST._IExpression _2039_on = _source99.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2040_field = _source99.dtor_field;
          bool _2041_isDatatype = _source99.dtor_onDatatype;
          bool _2042_isStatic = _source99.dtor_isStatic;
          BigInteger _2043_arity = _source99.dtor_arity;
          unmatched99 = false;
          {
            RAST._IExpr _2044_onExpr;
            DCOMP._IOwnership _2045_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2046_recIdents;
            RAST._IExpr _out510;
            DCOMP._IOwnership _out511;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out512;
            (this).GenExpr(_2039_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out510, out _out511, out _out512);
            _2044_onExpr = _out510;
            _2045_onOwned = _out511;
            _2046_recIdents = _out512;
            Dafny.ISequence<Dafny.Rune> _2047_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2048_onString;
            _2048_onString = (_2044_onExpr)._ToString(DCOMP.__default.IND);
            if (_2042_isStatic) {
              _2047_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2048_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_2040_field));
            } else {
              _2047_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2047_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2047_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2048_onString), ((object.Equals(_2045_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2049_args;
              _2049_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2050_i;
              _2050_i = BigInteger.Zero;
              while ((_2050_i) < (_2043_arity)) {
                if ((_2050_i).Sign == 1) {
                  _2049_args = Dafny.Sequence<Dafny.Rune>.Concat(_2049_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2049_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2049_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2050_i));
                _2050_i = (_2050_i) + (BigInteger.One);
              }
              _2047_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2047_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2049_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2047_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2047_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_2040_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2049_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2047_s = Dafny.Sequence<Dafny.Rune>.Concat(_2047_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2047_s = Dafny.Sequence<Dafny.Rune>.Concat(_2047_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2051_typeShape;
            _2051_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2052_i;
            _2052_i = BigInteger.Zero;
            while ((_2052_i) < (_2043_arity)) {
              if ((_2052_i).Sign == 1) {
                _2051_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2051_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2051_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2051_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2052_i = (_2052_i) + (BigInteger.One);
            }
            _2051_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2051_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2047_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2047_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2051_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2047_s);
            RAST._IExpr _out513;
            DCOMP._IOwnership _out514;
            (this).FromOwned(r, expectedOwnership, out _out513, out _out514);
            r = _out513;
            resultingOwnership = _out514;
            readIdents = _2046_recIdents;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_Select) {
          DAST._IExpression _2053_on = _source99.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2054_field = _source99.dtor_field;
          bool _2055_isConstant = _source99.dtor_isConstant;
          bool _2056_isDatatype = _source99.dtor_onDatatype;
          DAST._IType _2057_fieldType = _source99.dtor_fieldType;
          unmatched99 = false;
          {
            if (((_2053_on).is_Companion) || ((_2053_on).is_ExternCompanion)) {
              RAST._IExpr _2058_onExpr;
              DCOMP._IOwnership _2059_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2060_recIdents;
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out517;
              (this).GenExpr(_2053_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out515, out _out516, out _out517);
              _2058_onExpr = _out515;
              _2059_onOwned = _out516;
              _2060_recIdents = _out517;
              r = ((_2058_onExpr).MSel(DCOMP.__default.escapeName(_2054_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out518;
              DCOMP._IOwnership _out519;
              (this).FromOwned(r, expectedOwnership, out _out518, out _out519);
              r = _out518;
              resultingOwnership = _out519;
              readIdents = _2060_recIdents;
              return ;
            } else if (_2056_isDatatype) {
              RAST._IExpr _2061_onExpr;
              DCOMP._IOwnership _2062_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2063_recIdents;
              RAST._IExpr _out520;
              DCOMP._IOwnership _out521;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out522;
              (this).GenExpr(_2053_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out520, out _out521, out _out522);
              _2061_onExpr = _out520;
              _2062_onOwned = _out521;
              _2063_recIdents = _out522;
              r = ((_2061_onExpr).Sel(DCOMP.__default.escapeName(_2054_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2064_typ;
              RAST._IType _out523;
              _out523 = (this).GenType(_2057_fieldType, DCOMP.GenTypeContext.@default());
              _2064_typ = _out523;
              RAST._IExpr _out524;
              DCOMP._IOwnership _out525;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out524, out _out525);
              r = _out524;
              resultingOwnership = _out525;
              readIdents = _2063_recIdents;
            } else {
              RAST._IExpr _2065_onExpr;
              DCOMP._IOwnership _2066_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2067_recIdents;
              RAST._IExpr _out526;
              DCOMP._IOwnership _out527;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out528;
              (this).GenExpr(_2053_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out526, out _out527, out _out528);
              _2065_onExpr = _out526;
              _2066_onOwned = _out527;
              _2067_recIdents = _out528;
              r = _2065_onExpr;
              if (!object.Equals(_2065_onExpr, RAST.__default.self)) {
                RAST._IExpr _source101 = _2065_onExpr;
                bool unmatched101 = true;
                if (unmatched101) {
                  if (_source101.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source101.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source101.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name15 = underlying5.dtor_name;
                        if (object.Equals(name15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          unmatched101 = false;
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                        }
                      }
                    }
                  }
                }
                if (unmatched101) {
                  unmatched101 = false;
                }
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeName(_2054_field));
              if (_2055_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out529;
              DCOMP._IOwnership _out530;
              (this).FromOwned(r, expectedOwnership, out _out529, out _out530);
              r = _out529;
              resultingOwnership = _out530;
              readIdents = _2067_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_Index) {
          DAST._IExpression _2068_on = _source99.dtor_expr;
          DAST._ICollKind _2069_collKind = _source99.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2070_indices = _source99.dtor_indices;
          unmatched99 = false;
          {
            RAST._IExpr _2071_onExpr;
            DCOMP._IOwnership _2072_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2073_recIdents;
            RAST._IExpr _out531;
            DCOMP._IOwnership _out532;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
            (this).GenExpr(_2068_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out531, out _out532, out _out533);
            _2071_onExpr = _out531;
            _2072_onOwned = _out532;
            _2073_recIdents = _out533;
            readIdents = _2073_recIdents;
            r = _2071_onExpr;
            bool _2074_hadArray;
            _2074_hadArray = false;
            if (object.Equals(_2069_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2074_hadArray = true;
              if ((new BigInteger((_2070_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi47 = new BigInteger((_2070_indices).Count);
            for (BigInteger _2075_i = BigInteger.Zero; _2075_i < _hi47; _2075_i++) {
              if (object.Equals(_2069_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2076_idx;
                DCOMP._IOwnership _2077_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2078_recIdentsIdx;
                RAST._IExpr _out534;
                DCOMP._IOwnership _out535;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out536;
                (this).GenExpr((_2070_indices).Select(_2075_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out534, out _out535, out _out536);
                _2076_idx = _out534;
                _2077_idxOwned = _out535;
                _2078_recIdentsIdx = _out536;
                _2076_idx = RAST.__default.IntoUsize(_2076_idx);
                r = RAST.Expr.create_SelectIndex(r, _2076_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2078_recIdentsIdx);
              } else {
                RAST._IExpr _2079_idx;
                DCOMP._IOwnership _2080_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2081_recIdentsIdx;
                RAST._IExpr _out537;
                DCOMP._IOwnership _out538;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out539;
                (this).GenExpr((_2070_indices).Select(_2075_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out537, out _out538, out _out539);
                _2079_idx = _out537;
                _2080_idxOwned = _out538;
                _2081_recIdentsIdx = _out539;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2079_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2081_recIdentsIdx);
              }
            }
            if (_2074_hadArray) {
              r = (r).Clone();
            }
            RAST._IExpr _out540;
            DCOMP._IOwnership _out541;
            (this).FromOwned(r, expectedOwnership, out _out540, out _out541);
            r = _out540;
            resultingOwnership = _out541;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_IndexRange) {
          DAST._IExpression _2082_on = _source99.dtor_expr;
          bool _2083_isArray = _source99.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2084_low = _source99.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2085_high = _source99.dtor_high;
          unmatched99 = false;
          {
            RAST._IExpr _2086_onExpr;
            DCOMP._IOwnership _2087_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2088_recIdents;
            RAST._IExpr _out542;
            DCOMP._IOwnership _out543;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
            (this).GenExpr(_2082_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out542, out _out543, out _out544);
            _2086_onExpr = _out542;
            _2087_onOwned = _out543;
            _2088_recIdents = _out544;
            readIdents = _2088_recIdents;
            Dafny.ISequence<Dafny.Rune> _2089_methodName;
            _2089_methodName = (((_2084_low).is_Some) ? ((((_2085_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2085_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2090_arguments;
            _2090_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source102 = _2084_low;
            bool unmatched102 = true;
            if (unmatched102) {
              if (_source102.is_Some) {
                DAST._IExpression _2091_l = _source102.dtor_value;
                unmatched102 = false;
                {
                  RAST._IExpr _2092_lExpr;
                  DCOMP._IOwnership _2093___v193;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2094_recIdentsL;
                  RAST._IExpr _out545;
                  DCOMP._IOwnership _out546;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out547;
                  (this).GenExpr(_2091_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out545, out _out546, out _out547);
                  _2092_lExpr = _out545;
                  _2093___v193 = _out546;
                  _2094_recIdentsL = _out547;
                  _2090_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2090_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2092_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2094_recIdentsL);
                }
              }
            }
            if (unmatched102) {
              unmatched102 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source103 = _2085_high;
            bool unmatched103 = true;
            if (unmatched103) {
              if (_source103.is_Some) {
                DAST._IExpression _2095_h = _source103.dtor_value;
                unmatched103 = false;
                {
                  RAST._IExpr _2096_hExpr;
                  DCOMP._IOwnership _2097___v194;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2098_recIdentsH;
                  RAST._IExpr _out548;
                  DCOMP._IOwnership _out549;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out550;
                  (this).GenExpr(_2095_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out548, out _out549, out _out550);
                  _2096_hExpr = _out548;
                  _2097___v194 = _out549;
                  _2098_recIdentsH = _out550;
                  _2090_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2090_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2096_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2098_recIdentsH);
                }
              }
            }
            if (unmatched103) {
              unmatched103 = false;
            }
            r = _2086_onExpr;
            if (_2083_isArray) {
              if (!(_2089_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2089_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2089_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2089_methodName))).Apply(_2090_arguments);
            } else {
              if (!(_2089_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2089_methodName)).Apply(_2090_arguments);
              }
            }
            RAST._IExpr _out551;
            DCOMP._IOwnership _out552;
            (this).FromOwned(r, expectedOwnership, out _out551, out _out552);
            r = _out551;
            resultingOwnership = _out552;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_TupleSelect) {
          DAST._IExpression _2099_on = _source99.dtor_expr;
          BigInteger _2100_idx = _source99.dtor_index;
          DAST._IType _2101_fieldType = _source99.dtor_fieldType;
          unmatched99 = false;
          {
            RAST._IExpr _2102_onExpr;
            DCOMP._IOwnership _2103_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2104_recIdents;
            RAST._IExpr _out553;
            DCOMP._IOwnership _out554;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out555;
            (this).GenExpr(_2099_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out553, out _out554, out _out555);
            _2102_onExpr = _out553;
            _2103_onOwnership = _out554;
            _2104_recIdents = _out555;
            Dafny.ISequence<Dafny.Rune> _2105_selName;
            _2105_selName = Std.Strings.__default.OfNat(_2100_idx);
            DAST._IType _source104 = _2101_fieldType;
            bool unmatched104 = true;
            if (unmatched104) {
              if (_source104.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2106_tps = _source104.dtor_Tuple_a0;
                unmatched104 = false;
                if (((_2101_fieldType).is_Tuple) && ((new BigInteger((_2106_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2105_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2105_selName);
                }
              }
            }
            if (unmatched104) {
              unmatched104 = false;
            }
            r = ((_2102_onExpr).Sel(_2105_selName)).Clone();
            RAST._IExpr _out556;
            DCOMP._IOwnership _out557;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out556, out _out557);
            r = _out556;
            resultingOwnership = _out557;
            readIdents = _2104_recIdents;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_Call) {
          DAST._IExpression _2107_on = _source99.dtor_on;
          DAST._ICallName _2108_name = _source99.dtor_callName;
          Dafny.ISequence<DAST._IType> _2109_typeArgs = _source99.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2110_args = _source99.dtor_args;
          unmatched99 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2111_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2112_recIdents;
            Dafny.ISequence<RAST._IType> _2113_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2114_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out558;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out559;
            Dafny.ISequence<RAST._IType> _out560;
            Std.Wrappers._IOption<DAST._IResolvedType> _out561;
            (this).GenArgs(selfIdent, _2108_name, _2109_typeArgs, _2110_args, env, out _out558, out _out559, out _out560, out _out561);
            _2111_argExprs = _out558;
            _2112_recIdents = _out559;
            _2113_typeExprs = _out560;
            _2114_fullNameQualifier = _out561;
            readIdents = _2112_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source105 = _2114_fullNameQualifier;
            bool unmatched105 = true;
            if (unmatched105) {
              if (_source105.is_Some) {
                DAST._IResolvedType value11 = _source105.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2115_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2116_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2117_base = value11.dtor_kind;
                unmatched105 = false;
                RAST._IExpr _2118_fullPath;
                RAST._IExpr _out562;
                _out562 = DCOMP.COMP.GenPathExpr(_2115_path, true);
                _2118_fullPath = _out562;
                Dafny.ISequence<RAST._IType> _2119_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out563;
                _out563 = (this).GenTypeArgs(_2116_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2119_onTypeExprs = _out563;
                RAST._IExpr _2120_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2121_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2122_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2117_base).is_Trait) || ((_2117_base).is_Class)) {
                  RAST._IExpr _out564;
                  DCOMP._IOwnership _out565;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out566;
                  (this).GenExpr(_2107_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out564, out _out565, out _out566);
                  _2120_onExpr = _out564;
                  _2121_recOwnership = _out565;
                  _2122_recIdents = _out566;
                  _2120_onExpr = ((this).read__macro).Apply1(_2120_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2122_recIdents);
                } else {
                  RAST._IExpr _out567;
                  DCOMP._IOwnership _out568;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out569;
                  (this).GenExpr(_2107_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out567, out _out568, out _out569);
                  _2120_onExpr = _out567;
                  _2121_recOwnership = _out568;
                  _2122_recIdents = _out569;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2122_recIdents);
                }
                r = ((((_2118_fullPath).ApplyType(_2119_onTypeExprs)).MSel(DCOMP.__default.escapeName((_2108_name).dtor_name))).ApplyType(_2113_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2120_onExpr), _2111_argExprs));
                RAST._IExpr _out570;
                DCOMP._IOwnership _out571;
                (this).FromOwned(r, expectedOwnership, out _out570, out _out571);
                r = _out570;
                resultingOwnership = _out571;
              }
            }
            if (unmatched105) {
              unmatched105 = false;
              RAST._IExpr _2123_onExpr;
              DCOMP._IOwnership _2124___v200;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2125_recIdents;
              RAST._IExpr _out572;
              DCOMP._IOwnership _out573;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out574;
              (this).GenExpr(_2107_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out572, out _out573, out _out574);
              _2123_onExpr = _out572;
              _2124___v200 = _out573;
              _2125_recIdents = _out574;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2125_recIdents);
              Dafny.ISequence<Dafny.Rune> _2126_renderedName;
              _2126_renderedName = (this).GetMethodName(_2107_on, _2108_name);
              DAST._IExpression _source106 = _2107_on;
              bool unmatched106 = true;
              if (unmatched106) {
                bool disjunctiveMatch16 = false;
                if (_source106.is_Companion) {
                  disjunctiveMatch16 = true;
                }
                if (_source106.is_ExternCompanion) {
                  disjunctiveMatch16 = true;
                }
                if (disjunctiveMatch16) {
                  unmatched106 = false;
                  {
                    _2123_onExpr = (_2123_onExpr).MSel(_2126_renderedName);
                  }
                }
              }
              if (unmatched106) {
                unmatched106 = false;
                {
                  if (!object.Equals(_2123_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source107 = _2108_name;
                    bool unmatched107 = true;
                    if (unmatched107) {
                      if (_source107.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source107.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2127_tpe = onType2.dtor_value;
                          unmatched107 = false;
                          RAST._IType _2128_typ;
                          RAST._IType _out575;
                          _out575 = (this).GenType(_2127_tpe, DCOMP.GenTypeContext.@default());
                          _2128_typ = _out575;
                          if ((_2128_typ).IsObjectOrPointer()) {
                            _2123_onExpr = ((this).read__macro).Apply1(_2123_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched107) {
                      unmatched107 = false;
                    }
                  }
                  _2123_onExpr = (_2123_onExpr).Sel(_2126_renderedName);
                }
              }
              r = ((_2123_onExpr).ApplyType(_2113_typeExprs)).Apply(_2111_argExprs);
              RAST._IExpr _out576;
              DCOMP._IOwnership _out577;
              (this).FromOwned(r, expectedOwnership, out _out576, out _out577);
              r = _out576;
              resultingOwnership = _out577;
              return ;
            }
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2129_paramsDafny = _source99.dtor_params;
          DAST._IType _2130_retType = _source99.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2131_body = _source99.dtor_body;
          unmatched99 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2132_params;
            Dafny.ISequence<RAST._IFormal> _out578;
            _out578 = (this).GenParams(_2129_paramsDafny);
            _2132_params = _out578;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2133_paramNames;
            _2133_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2134_paramTypesMap;
            _2134_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi48 = new BigInteger((_2132_params).Count);
            for (BigInteger _2135_i = BigInteger.Zero; _2135_i < _hi48; _2135_i++) {
              Dafny.ISequence<Dafny.Rune> _2136_name;
              _2136_name = ((_2132_params).Select(_2135_i)).dtor_name;
              _2133_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2133_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2136_name));
              _2134_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2134_paramTypesMap, _2136_name, ((_2132_params).Select(_2135_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2137_subEnv;
            _2137_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2133_paramNames, _2134_paramTypesMap));
            RAST._IExpr _2138_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2139_recIdents;
            DCOMP._IEnvironment _2140___v209;
            RAST._IExpr _out579;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out580;
            DCOMP._IEnvironment _out581;
            (this).GenStmts(_2131_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2137_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out579, out _out580, out _out581);
            _2138_recursiveGen = _out579;
            _2139_recIdents = _out580;
            _2140___v209 = _out581;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2139_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2139_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2141_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll7 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_7 in (_2141_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2142_name = (Dafny.ISequence<Dafny.Rune>)_compr_7;
                if ((_2141_paramNames).Contains(_2142_name)) {
                  _coll7.Add(_2142_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll7);
            }))())(_2133_paramNames));
            RAST._IExpr _2143_allReadCloned;
            _2143_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2139_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2144_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2139_recIdents).Elements) {
                _2144_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_2139_recIdents).Contains(_2144_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 5004)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2144_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2145_selfCloned;
                DCOMP._IOwnership _2146___v210;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2147___v211;
                RAST._IExpr _out582;
                DCOMP._IOwnership _out583;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out584;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out582, out _out583, out _out584);
                _2145_selfCloned = _out582;
                _2146___v210 = _out583;
                _2147___v211 = _out584;
                _2143_allReadCloned = (_2143_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2145_selfCloned)));
              } else if (!((_2133_paramNames).Contains(_2144_next))) {
                RAST._IExpr _2148_copy;
                _2148_copy = (RAST.Expr.create_Identifier(_2144_next)).Clone();
                _2143_allReadCloned = (_2143_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2144_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2148_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2144_next));
              }
              _2139_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2139_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2144_next));
            }
            RAST._IType _2149_retTypeGen;
            RAST._IType _out585;
            _out585 = (this).GenType(_2130_retType, DCOMP.GenTypeContext.InFn());
            _2149_retTypeGen = _out585;
            r = RAST.Expr.create_Block((_2143_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2132_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2149_retTypeGen), RAST.Expr.create_Block(_2138_recursiveGen)))));
            RAST._IExpr _out586;
            DCOMP._IOwnership _out587;
            (this).FromOwned(r, expectedOwnership, out _out586, out _out587);
            r = _out586;
            resultingOwnership = _out587;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2150_values = _source99.dtor_values;
          DAST._IType _2151_retType = _source99.dtor_retType;
          DAST._IExpression _2152_expr = _source99.dtor_expr;
          unmatched99 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2153_paramNames;
            _2153_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2154_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out588;
            _out588 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2155_value) => {
              return (_2155_value).dtor__0;
            })), _2150_values));
            _2154_paramFormals = _out588;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2156_paramTypes;
            _2156_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2157_paramNamesSet;
            _2157_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi49 = new BigInteger((_2150_values).Count);
            for (BigInteger _2158_i = BigInteger.Zero; _2158_i < _hi49; _2158_i++) {
              Dafny.ISequence<Dafny.Rune> _2159_name;
              _2159_name = (((_2150_values).Select(_2158_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2160_rName;
              _2160_rName = DCOMP.__default.escapeName(_2159_name);
              _2153_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2153_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2160_rName));
              _2156_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2156_paramTypes, _2160_rName, ((_2154_paramFormals).Select(_2158_i)).dtor_tpe);
              _2157_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2157_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2160_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi50 = new BigInteger((_2150_values).Count);
            for (BigInteger _2161_i = BigInteger.Zero; _2161_i < _hi50; _2161_i++) {
              RAST._IType _2162_typeGen;
              RAST._IType _out589;
              _out589 = (this).GenType((((_2150_values).Select(_2161_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2162_typeGen = _out589;
              RAST._IExpr _2163_valueGen;
              DCOMP._IOwnership _2164___v212;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2165_recIdents;
              RAST._IExpr _out590;
              DCOMP._IOwnership _out591;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out592;
              (this).GenExpr(((_2150_values).Select(_2161_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out590, out _out591, out _out592);
              _2163_valueGen = _out590;
              _2164___v212 = _out591;
              _2165_recIdents = _out592;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_2150_values).Select(_2161_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2162_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2163_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2165_recIdents);
            }
            DCOMP._IEnvironment _2166_newEnv;
            _2166_newEnv = DCOMP.Environment.create(_2153_paramNames, _2156_paramTypes);
            RAST._IExpr _2167_recGen;
            DCOMP._IOwnership _2168_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2169_recIdents;
            RAST._IExpr _out593;
            DCOMP._IOwnership _out594;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out595;
            (this).GenExpr(_2152_expr, selfIdent, _2166_newEnv, expectedOwnership, out _out593, out _out594, out _out595);
            _2167_recGen = _out593;
            _2168_recOwned = _out594;
            _2169_recIdents = _out595;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2169_recIdents, _2157_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2167_recGen));
            RAST._IExpr _out596;
            DCOMP._IOwnership _out597;
            (this).FromOwnership(r, _2168_recOwned, expectedOwnership, out _out596, out _out597);
            r = _out596;
            resultingOwnership = _out597;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2170_name = _source99.dtor_ident;
          DAST._IType _2171_tpe = _source99.dtor_typ;
          DAST._IExpression _2172_value = _source99.dtor_value;
          DAST._IExpression _2173_iifeBody = _source99.dtor_iifeBody;
          unmatched99 = false;
          {
            RAST._IExpr _2174_valueGen;
            DCOMP._IOwnership _2175___v213;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2176_recIdents;
            RAST._IExpr _out598;
            DCOMP._IOwnership _out599;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out600;
            (this).GenExpr(_2172_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out598, out _out599, out _out600);
            _2174_valueGen = _out598;
            _2175___v213 = _out599;
            _2176_recIdents = _out600;
            readIdents = _2176_recIdents;
            RAST._IType _2177_valueTypeGen;
            RAST._IType _out601;
            _out601 = (this).GenType(_2171_tpe, DCOMP.GenTypeContext.InFn());
            _2177_valueTypeGen = _out601;
            RAST._IExpr _2178_bodyGen;
            DCOMP._IOwnership _2179___v214;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2180_bodyIdents;
            RAST._IExpr _out602;
            DCOMP._IOwnership _out603;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out604;
            (this).GenExpr(_2173_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out602, out _out603, out _out604);
            _2178_bodyGen = _out602;
            _2179___v214 = _out603;
            _2180_bodyIdents = _out604;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2180_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_2170_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_2170_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_2177_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2174_valueGen))).Then(_2178_bodyGen));
            RAST._IExpr _out605;
            DCOMP._IOwnership _out606;
            (this).FromOwned(r, expectedOwnership, out _out605, out _out606);
            r = _out605;
            resultingOwnership = _out606;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_Apply) {
          DAST._IExpression _2181_func = _source99.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2182_args = _source99.dtor_args;
          unmatched99 = false;
          {
            RAST._IExpr _2183_funcExpr;
            DCOMP._IOwnership _2184___v215;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2185_recIdents;
            RAST._IExpr _out607;
            DCOMP._IOwnership _out608;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out609;
            (this).GenExpr(_2181_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out607, out _out608, out _out609);
            _2183_funcExpr = _out607;
            _2184___v215 = _out608;
            _2185_recIdents = _out609;
            readIdents = _2185_recIdents;
            Dafny.ISequence<RAST._IExpr> _2186_rArgs;
            _2186_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi51 = new BigInteger((_2182_args).Count);
            for (BigInteger _2187_i = BigInteger.Zero; _2187_i < _hi51; _2187_i++) {
              RAST._IExpr _2188_argExpr;
              DCOMP._IOwnership _2189_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2190_argIdents;
              RAST._IExpr _out610;
              DCOMP._IOwnership _out611;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out612;
              (this).GenExpr((_2182_args).Select(_2187_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out610, out _out611, out _out612);
              _2188_argExpr = _out610;
              _2189_argOwned = _out611;
              _2190_argIdents = _out612;
              _2186_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2186_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2188_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2190_argIdents);
            }
            r = (_2183_funcExpr).Apply(_2186_rArgs);
            RAST._IExpr _out613;
            DCOMP._IOwnership _out614;
            (this).FromOwned(r, expectedOwnership, out _out613, out _out614);
            r = _out613;
            resultingOwnership = _out614;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_TypeTest) {
          DAST._IExpression _2191_on = _source99.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2192_dType = _source99.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2193_variant = _source99.dtor_variant;
          unmatched99 = false;
          {
            RAST._IExpr _2194_exprGen;
            DCOMP._IOwnership _2195___v216;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2196_recIdents;
            RAST._IExpr _out615;
            DCOMP._IOwnership _out616;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out617;
            (this).GenExpr(_2191_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out615, out _out616, out _out617);
            _2194_exprGen = _out615;
            _2195___v216 = _out616;
            _2196_recIdents = _out617;
            RAST._IType _2197_dTypePath;
            RAST._IType _out618;
            _out618 = DCOMP.COMP.GenPath(_2192_dType);
            _2197_dTypePath = _out618;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2194_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2197_dTypePath).MSel(DCOMP.__default.escapeName(_2193_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out619;
            DCOMP._IOwnership _out620;
            (this).FromOwned(r, expectedOwnership, out _out619, out _out620);
            r = _out619;
            resultingOwnership = _out620;
            readIdents = _2196_recIdents;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_BoolBoundedPool) {
          unmatched99 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out621;
            DCOMP._IOwnership _out622;
            (this).FromOwned(r, expectedOwnership, out _out621, out _out622);
            r = _out621;
            resultingOwnership = _out622;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_SetBoundedPool) {
          DAST._IExpression _2198_of = _source99.dtor_of;
          unmatched99 = false;
          {
            RAST._IExpr _2199_exprGen;
            DCOMP._IOwnership _2200___v217;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2201_recIdents;
            RAST._IExpr _out623;
            DCOMP._IOwnership _out624;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out625;
            (this).GenExpr(_2198_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out623, out _out624, out _out625);
            _2199_exprGen = _out623;
            _2200___v217 = _out624;
            _2201_recIdents = _out625;
            r = ((_2199_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out626;
            DCOMP._IOwnership _out627;
            (this).FromOwned(r, expectedOwnership, out _out626, out _out627);
            r = _out626;
            resultingOwnership = _out627;
            readIdents = _2201_recIdents;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_SeqBoundedPool) {
          DAST._IExpression _2202_of = _source99.dtor_of;
          bool _2203_includeDuplicates = _source99.dtor_includeDuplicates;
          unmatched99 = false;
          {
            RAST._IExpr _2204_exprGen;
            DCOMP._IOwnership _2205___v218;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2206_recIdents;
            RAST._IExpr _out628;
            DCOMP._IOwnership _out629;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out630;
            (this).GenExpr(_2202_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out628, out _out629, out _out630);
            _2204_exprGen = _out628;
            _2205___v218 = _out629;
            _2206_recIdents = _out630;
            r = ((_2204_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2203_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out631;
            DCOMP._IOwnership _out632;
            (this).FromOwned(r, expectedOwnership, out _out631, out _out632);
            r = _out631;
            resultingOwnership = _out632;
            readIdents = _2206_recIdents;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_MapBoundedPool) {
          DAST._IExpression _2207_of = _source99.dtor_of;
          unmatched99 = false;
          {
            RAST._IExpr _2208_exprGen;
            DCOMP._IOwnership _2209___v219;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2210_recIdents;
            RAST._IExpr _out633;
            DCOMP._IOwnership _out634;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out635;
            (this).GenExpr(_2207_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out633, out _out634, out _out635);
            _2208_exprGen = _out633;
            _2209___v219 = _out634;
            _2210_recIdents = _out635;
            r = ((((_2208_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2210_recIdents;
            RAST._IExpr _out636;
            DCOMP._IOwnership _out637;
            (this).FromOwned(r, expectedOwnership, out _out636, out _out637);
            r = _out636;
            resultingOwnership = _out637;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_IntRange) {
          DAST._IExpression _2211_lo = _source99.dtor_lo;
          DAST._IExpression _2212_hi = _source99.dtor_hi;
          bool _2213_up = _source99.dtor_up;
          unmatched99 = false;
          {
            RAST._IExpr _2214_lo;
            DCOMP._IOwnership _2215___v220;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2216_recIdentsLo;
            RAST._IExpr _out638;
            DCOMP._IOwnership _out639;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out640;
            (this).GenExpr(_2211_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out638, out _out639, out _out640);
            _2214_lo = _out638;
            _2215___v220 = _out639;
            _2216_recIdentsLo = _out640;
            RAST._IExpr _2217_hi;
            DCOMP._IOwnership _2218___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2219_recIdentsHi;
            RAST._IExpr _out641;
            DCOMP._IOwnership _out642;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out643;
            (this).GenExpr(_2212_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out641, out _out642, out _out643);
            _2217_hi = _out641;
            _2218___v221 = _out642;
            _2219_recIdentsHi = _out643;
            if (_2213_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2214_lo, _2217_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2217_hi, _2214_lo));
            }
            RAST._IExpr _out644;
            DCOMP._IOwnership _out645;
            (this).FromOwned(r, expectedOwnership, out _out644, out _out645);
            r = _out644;
            resultingOwnership = _out645;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2216_recIdentsLo, _2219_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_UnboundedIntRange) {
          DAST._IExpression _2220_start = _source99.dtor_start;
          bool _2221_up = _source99.dtor_up;
          unmatched99 = false;
          {
            RAST._IExpr _2222_start;
            DCOMP._IOwnership _2223___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2224_recIdentStart;
            RAST._IExpr _out646;
            DCOMP._IOwnership _out647;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out648;
            (this).GenExpr(_2220_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out646, out _out647, out _out648);
            _2222_start = _out646;
            _2223___v222 = _out647;
            _2224_recIdentStart = _out648;
            if (_2221_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2222_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2222_start);
            }
            RAST._IExpr _out649;
            DCOMP._IOwnership _out650;
            (this).FromOwned(r, expectedOwnership, out _out649, out _out650);
            r = _out649;
            resultingOwnership = _out650;
            readIdents = _2224_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_MapBuilder) {
          DAST._IType _2225_keyType = _source99.dtor_keyType;
          DAST._IType _2226_valueType = _source99.dtor_valueType;
          unmatched99 = false;
          {
            RAST._IType _2227_kType;
            RAST._IType _out651;
            _out651 = (this).GenType(_2225_keyType, DCOMP.GenTypeContext.@default());
            _2227_kType = _out651;
            RAST._IType _2228_vType;
            RAST._IType _out652;
            _out652 = (this).GenType(_2226_valueType, DCOMP.GenTypeContext.@default());
            _2228_vType = _out652;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2227_kType, _2228_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out653;
            DCOMP._IOwnership _out654;
            (this).FromOwned(r, expectedOwnership, out _out653, out _out654);
            r = _out653;
            resultingOwnership = _out654;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched99) {
        if (_source99.is_SetBuilder) {
          DAST._IType _2229_elemType = _source99.dtor_elemType;
          unmatched99 = false;
          {
            RAST._IType _2230_eType;
            RAST._IType _out655;
            _out655 = (this).GenType(_2229_elemType, DCOMP.GenTypeContext.@default());
            _2230_eType = _out655;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2230_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out656;
            DCOMP._IOwnership _out657;
            (this).FromOwned(r, expectedOwnership, out _out656, out _out657);
            r = _out656;
            resultingOwnership = _out657;
            return ;
          }
        }
      }
      if (unmatched99) {
        DAST._IType _2231_elemType = _source99.dtor_elemType;
        DAST._IExpression _2232_collection = _source99.dtor_collection;
        bool _2233_is__forall = _source99.dtor_is__forall;
        DAST._IExpression _2234_lambda = _source99.dtor_lambda;
        unmatched99 = false;
        {
          RAST._IType _2235_tpe;
          RAST._IType _out658;
          _out658 = (this).GenType(_2231_elemType, DCOMP.GenTypeContext.@default());
          _2235_tpe = _out658;
          RAST._IExpr _2236_collectionGen;
          DCOMP._IOwnership _2237___v223;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2238_recIdents;
          RAST._IExpr _out659;
          DCOMP._IOwnership _out660;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out661;
          (this).GenExpr(_2232_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out659, out _out660, out _out661);
          _2236_collectionGen = _out659;
          _2237___v223 = _out660;
          _2238_recIdents = _out661;
          Dafny.ISequence<DAST._IAttribute> _2239_extraAttributes;
          _2239_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2232_collection).is_IntRange) || ((_2232_collection).is_UnboundedIntRange)) || ((_2232_collection).is_SeqBoundedPool)) {
            _2239_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2234_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2240_formals;
            _2240_formals = (_2234_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2241_newFormals;
            _2241_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi52 = new BigInteger((_2240_formals).Count);
            for (BigInteger _2242_i = BigInteger.Zero; _2242_i < _hi52; _2242_i++) {
              var _pat_let_tv144 = _2239_extraAttributes;
              var _pat_let_tv145 = _2240_formals;
              _2241_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2241_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2240_formals).Select(_2242_i), _pat_let38_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let38_0, _2243_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv144, ((_pat_let_tv145).Select(_2242_i)).dtor_attributes), _pat_let39_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let39_0, _2244_dt__update_hattributes_h0 => DAST.Formal.create((_2243_dt__update__tmp_h0).dtor_name, (_2243_dt__update__tmp_h0).dtor_typ, _2244_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv146 = _2241_newFormals;
            DAST._IExpression _2245_newLambda;
            _2245_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2234_lambda, _pat_let40_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let40_0, _2246_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv146, _pat_let41_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let41_0, _2247_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2247_dt__update_hparams_h0, (_2246_dt__update__tmp_h1).dtor_retType, (_2246_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2248_lambdaGen;
            DCOMP._IOwnership _2249___v224;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2250_recLambdaIdents;
            RAST._IExpr _out662;
            DCOMP._IOwnership _out663;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out664;
            (this).GenExpr(_2245_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out662, out _out663, out _out664);
            _2248_lambdaGen = _out662;
            _2249___v224 = _out663;
            _2250_recLambdaIdents = _out664;
            Dafny.ISequence<Dafny.Rune> _2251_fn;
            _2251_fn = ((_2233_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2236_collectionGen).Sel(_2251_fn)).Apply1(((_2248_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2238_recIdents, _2250_recLambdaIdents);
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Quantifier without an inline lambda"));
            r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
          RAST._IExpr _out665;
          DCOMP._IOwnership _out666;
          (this).FromOwned(r, expectedOwnership, out _out665, out _out666);
          r = _out665;
          resultingOwnership = _out666;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> externalFiles)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      Dafny.ISequence<RAST._IModDecl> _2252_externUseDecls;
      _2252_externUseDecls = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi53 = new BigInteger((externalFiles).Count);
      for (BigInteger _2253_i = BigInteger.Zero; _2253_i < _hi53; _2253_i++) {
        Dafny.ISequence<Dafny.Rune> _2254_externalFile;
        _2254_externalFile = (externalFiles).Select(_2253_i);
        Dafny.ISequence<Dafny.Rune> _2255_externalMod;
        _2255_externalMod = _2254_externalFile;
        if (((new BigInteger((_2254_externalFile).Count)) > (new BigInteger(3))) && (((_2254_externalFile).Drop((new BigInteger((_2254_externalFile).Count)) - (new BigInteger(3)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".rs")))) {
          _2255_externalMod = (_2254_externalFile).Subsequence(BigInteger.Zero, (new BigInteger((_2254_externalFile).Count)) - (new BigInteger(3)));
        } else {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unrecognized external file "), _2254_externalFile), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". External file must be *.rs files")));
        }
        RAST._IMod _2256_externMod;
        _2256_externMod = RAST.Mod.create_ExternMod(_2255_externalMod);
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (_2256_externMod)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        _2252_externUseDecls = Dafny.Sequence<RAST._IModDecl>.Concat(_2252_externUseDecls, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), ((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"))).MSel(_2255_externalMod)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))));
      }
      if (!(_2252_externUseDecls).Equals(Dafny.Sequence<RAST._IModDecl>.FromElements())) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (RAST.Mod.create_Mod(DCOMP.COMP.DAFNY__EXTERN__MODULE, _2252_externUseDecls))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
      }
      BigInteger _hi54 = new BigInteger((p).Count);
      for (BigInteger _2257_i = BigInteger.Zero; _2257_i < _hi54; _2257_i++) {
        RAST._IMod _2258_m;
        RAST._IMod _out667;
        _out667 = (this).GenModule((p).Select(_2257_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2258_m = _out667;
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (_2258_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2259_i;
      _2259_i = BigInteger.Zero;
      while ((_2259_i) < (new BigInteger((fullName).Count))) {
        if ((_2259_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2259_i)));
        _2259_i = (_2259_i) + (BigInteger.One);
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