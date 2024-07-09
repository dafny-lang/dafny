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
            Dafny.ISequence<Dafny.Rune> _in135 = (i).Drop(new BigInteger(2));
            i = _in135;
            goto TAIL_CALL_START;
          }
        } else {
          return true;
        }
      } else {
        Dafny.ISequence<Dafny.Rune> _in136 = (i).Drop(BigInteger.One);
        i = _in136;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> idiomatic__rust(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1300___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1300___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1300___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1300___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in137 = (i).Drop(new BigInteger(2));
        i = _in137;
        goto TAIL_CALL_START;
      } else {
        _1300___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1300___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in138 = (i).Drop(BigInteger.One);
        i = _in138;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1301___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1301___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1301___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1301___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in139 = (i).Drop(BigInteger.One);
        i = _in139;
        goto TAIL_CALL_START;
      } else {
        _1301___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1301___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in140 = (i).Drop(BigInteger.One);
        i = _in140;
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
        Dafny.ISequence<Dafny.Rune> _1302_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1302_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeVar(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1303_r = (f);
      if ((DCOMP.__default.reserved__vars).Contains(_1303_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1303_r);
      } else {
        return DCOMP.__default.escapeIdent((f));
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
      var _pat_let_tv193 = dafnyName;
      var _pat_let_tv194 = rs;
      var _pat_let_tv195 = dafnyName;
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _1304_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source63 = (rs).Select(BigInteger.Zero);
          bool unmatched63 = true;
          if (unmatched63) {
            if (_source63.is_UserDefined) {
              DAST._IResolvedType _1305_resolvedType = _source63.dtor_resolved;
              unmatched63 = false;
              return DCOMP.__default.TraitTypeContainingMethod(_1305_resolvedType, _pat_let_tv193);
            }
          }
          if (unmatched63) {
            unmatched63 = false;
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
          throw new System.Exception("unexpected control point");
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source64 = _1304_res;
        bool unmatched64 = true;
        if (unmatched64) {
          if (_source64.is_Some) {
            unmatched64 = false;
            return _1304_res;
          }
        }
        if (unmatched64) {
          unmatched64 = false;
          return DCOMP.__default.TraitTypeContainingMethodAux((_pat_let_tv194).Drop(BigInteger.One), _pat_let_tv195);
        }
        throw new System.Exception("unexpected control point");
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethod(DAST._IResolvedType r, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DAST._IResolvedType _let_tmp_rhs53 = r;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1306_path = _let_tmp_rhs53.dtor_path;
      Dafny.ISequence<DAST._IType> _1307_typeArgs = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedTypeBase _1308_kind = _let_tmp_rhs53.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1309_attributes = _let_tmp_rhs53.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1310_properMethods = _let_tmp_rhs53.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1311_extendedTypes = _let_tmp_rhs53.dtor_extendedTypes;
      if ((_1310_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1311_extendedTypes, dafnyName);
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
      Dafny.ISequence<Dafny.Rune> _1312___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1312___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((s).Select(BigInteger.Zero)) == (new Dafny.Rune(' '))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1312___accumulator, s);
      } else {
        _1312___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1312___accumulator, ((((s).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")) : (Dafny.Sequence<Dafny.Rune>.FromElements((s).Select(BigInteger.Zero)))));
        Dafny.ISequence<Dafny.Rune> _in141 = (s).Drop(BigInteger.One);
        s = _in141;
        goto TAIL_CALL_START;
      }
    }
    public static DCOMP._IExternAttribute ExtractExtern(Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DCOMP._IExternAttribute res = DCOMP.ExternAttribute.Default();
      BigInteger _hi5 = new BigInteger((attributes).Count);
      for (BigInteger _1313_i = BigInteger.Zero; _1313_i < _hi5; _1313_i++) {
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _1314_attr;
        _1314_attr = DCOMP.__default.OptExtern((attributes).Select(_1313_i), dafnyName);
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _source65 = _1314_attr;
        bool unmatched65 = true;
        if (unmatched65) {
          if (_source65.is_Some) {
            DCOMP._IExternAttribute _1315_n = _source65.dtor_value;
            unmatched65 = false;
            res = _1315_n;
            return res;
          }
        }
        if (unmatched65) {
          unmatched65 = false;
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
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__vars { get {
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
      DCOMP._IEnvironment _1316_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1317_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll8 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_9 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1318_k = (Dafny.ISequence<Dafny.Rune>)_compr_9;
          if (((this).dtor_types).Contains(_1318_k)) {
            _coll8.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_1318_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_1318_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll8);
      }))();
      return DCOMP.Environment.create((_1316_dt__update__tmp_h0).dtor_names, _1317_dt__update_htypes_h0);
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
      BigInteger _1319_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1319_indexInEnv), ((this).dtor_names).Drop((_1319_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      this.optimizations = Dafny.Sequence<Func<RAST._IMod, RAST._IMod>>.Empty;
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
    public Dafny.ISequence<Func<RAST._IMod, RAST._IMod>> optimizations {get; set;}
    public void __ctor(bool unicodeChars, DCOMP._IObjectType objectType)
    {
      (this)._UnicodeChars = unicodeChars;
      (this)._ObjectType = objectType;
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
      (this).optimizations = Dafny.Sequence<Func<RAST._IMod, RAST._IMod>>.FromElements(FactorPathsOptimization.__default.apply);
      if ((objectType).is_RawPointers) {
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Raw pointers need to be wrapped in a newtype so that their equality has the semantics of Dafny (e.g. a class pointer and a trait pointer are equal), not Rust."));
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> ContainingPathToRust(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath) {
      return Std.Collections.Seq.__default.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1320_i) => {
        return DCOMP.__default.escapeName((_1320_i));
      })), containingPath);
    }
    public DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> s = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Default();
      _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs54 = DafnyCompilerRustUtils.__default.DafnyNameToContainingPathAndName((mod).dtor_name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1321_innerPath = _let_tmp_rhs54.dtor__0;
      Dafny.ISequence<Dafny.Rune> _1322_innerName = _let_tmp_rhs54.dtor__1;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1323_containingPath;
      _1323_containingPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, _1321_innerPath);
      Dafny.ISequence<Dafny.Rune> _1324_modName;
      _1324_modName = DCOMP.__default.escapeName(_1322_innerName);
      if (((mod).dtor_body).is_None) {
        s = DafnyCompilerRustUtils.GatheringModule.Wrap(DCOMP.COMP.ContainingPathToRust(_1323_containingPath), RAST.Mod.create_ExternMod(_1324_modName));
      } else {
        DCOMP._IExternAttribute _1325_optExtern;
        _1325_optExtern = DCOMP.__default.ExtractExternMod(mod);
        Dafny.ISequence<RAST._IModDecl> _1326_body;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _1327_allmodules;
        Dafny.ISequence<RAST._IModDecl> _out15;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out16;
        (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1323_containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1322_innerName)), out _out15, out _out16);
        _1326_body = _out15;
        _1327_allmodules = _out16;
        if ((_1325_optExtern).is_SimpleExtern) {
          if ((mod).dtor_requiresExterns) {
            _1326_body = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (((RAST.__default.crate).MSel(DCOMP.COMP.DAFNY__EXTERN__MODULE)).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1325_optExtern).dtor_overrideName))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))), _1326_body);
          }
        } else if ((_1325_optExtern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Externs on modules can only have 1 string argument"));
        } else if ((_1325_optExtern).is_UnsupportedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some((_1325_optExtern).dtor_reason);
        }
        s = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(DafnyCompilerRustUtils.GatheringModule.Wrap(DCOMP.COMP.ContainingPathToRust(_1323_containingPath), RAST.Mod.create_Mod(_1324_modName, _1326_body)), _1327_allmodules);
      }
      return s;
    }
    public void GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath, out Dafny.ISequence<RAST._IModDecl> s, out DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> allmodules)
    {
      s = Dafny.Sequence<RAST._IModDecl>.Empty;
      allmodules = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Default();
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      allmodules = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Empty();
      BigInteger _hi6 = new BigInteger((body).Count);
      for (BigInteger _1328_i = BigInteger.Zero; _1328_i < _hi6; _1328_i++) {
        Dafny.ISequence<RAST._IModDecl> _1329_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source66 = (body).Select(_1328_i);
        bool unmatched66 = true;
        if (unmatched66) {
          if (_source66.is_Module) {
            DAST._IModule _1330_m = _source66.dtor_Module_a0;
            unmatched66 = false;
            DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _1331_mm;
            DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out17;
            _out17 = (this).GenModule(_1330_m, containingPath);
            _1331_mm = _out17;
            allmodules = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(allmodules, _1331_mm);
            _1329_generated = Dafny.Sequence<RAST._IModDecl>.FromElements();
          }
        }
        if (unmatched66) {
          if (_source66.is_Class) {
            DAST._IClass _1332_c = _source66.dtor_Class_a0;
            unmatched66 = false;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenClass(_1332_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1332_c).dtor_name)));
            _1329_generated = _out18;
          }
        }
        if (unmatched66) {
          if (_source66.is_Trait) {
            DAST._ITrait _1333_t = _source66.dtor_Trait_a0;
            unmatched66 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenTrait(_1333_t, containingPath);
            _1329_generated = _out19;
          }
        }
        if (unmatched66) {
          if (_source66.is_Newtype) {
            DAST._INewtype _1334_n = _source66.dtor_Newtype_a0;
            unmatched66 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenNewtype(_1334_n);
            _1329_generated = _out20;
          }
        }
        if (unmatched66) {
          if (_source66.is_SynonymType) {
            DAST._ISynonymType _1335_s = _source66.dtor_SynonymType_a0;
            unmatched66 = false;
            Dafny.ISequence<RAST._IModDecl> _out21;
            _out21 = (this).GenSynonymType(_1335_s);
            _1329_generated = _out21;
          }
        }
        if (unmatched66) {
          DAST._IDatatype _1336_d = _source66.dtor_Datatype_a0;
          unmatched66 = false;
          Dafny.ISequence<RAST._IModDecl> _out22;
          _out22 = (this).GenDatatype(_1336_d);
          _1329_generated = _out22;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1329_generated);
      }
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1337_genTpConstraint;
      _1337_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1337_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1337_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1337_genTpConstraint);
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
        for (BigInteger _1338_tpI = BigInteger.Zero; _1338_tpI < _hi7; _1338_tpI++) {
          DAST._ITypeArgDecl _1339_tp;
          _1339_tp = (@params).Select(_1338_tpI);
          DAST._IType _1340_typeArg;
          RAST._ITypeParamDecl _1341_typeParam;
          DAST._IType _out23;
          RAST._ITypeParamDecl _out24;
          (this).GenTypeParam(_1339_tp, out _out23, out _out24);
          _1340_typeArg = _out23;
          _1341_typeParam = _out24;
          RAST._IType _1342_rType;
          RAST._IType _out25;
          _out25 = (this).GenType(_1340_typeArg, DCOMP.GenTypeContext.@default());
          _1342_rType = _out25;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1340_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1342_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1341_typeParam));
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
      Dafny.ISequence<DAST._IType> _1343_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1344_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1345_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1346_whereConstraints;
      Dafny.ISequence<DAST._IType> _out26;
      Dafny.ISequence<RAST._IType> _out27;
      Dafny.ISequence<RAST._ITypeParamDecl> _out28;
      Dafny.ISequence<Dafny.Rune> _out29;
      (this).GenTypeParameters((c).dtor_typeParams, out _out26, out _out27, out _out28, out _out29);
      _1343_typeParamsSeq = _out26;
      _1344_rTypeParams = _out27;
      _1345_rTypeParamsDecls = _out28;
      _1346_whereConstraints = _out29;
      Dafny.ISequence<Dafny.Rune> _1347_constrainedTypeParams;
      _1347_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1345_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1348_fields;
      _1348_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1349_fieldInits;
      _1349_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi8 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1350_fieldI = BigInteger.Zero; _1350_fieldI < _hi8; _1350_fieldI++) {
        DAST._IField _1351_field;
        _1351_field = ((c).dtor_fields).Select(_1350_fieldI);
        RAST._IType _1352_fieldType;
        RAST._IType _out30;
        _out30 = (this).GenType(((_1351_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1352_fieldType = _out30;
        Dafny.ISequence<Dafny.Rune> _1353_fieldRustName;
        _1353_fieldRustName = DCOMP.__default.escapeVar(((_1351_field).dtor_formal).dtor_name);
        _1348_fields = Dafny.Sequence<RAST._IField>.Concat(_1348_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1353_fieldRustName, _1352_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source67 = (_1351_field).dtor_defaultValue;
        bool unmatched67 = true;
        if (unmatched67) {
          if (_source67.is_Some) {
            DAST._IExpression _1354_e = _source67.dtor_value;
            unmatched67 = false;
            {
              RAST._IExpr _1355_expr;
              DCOMP._IOwnership _1356___v50;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1357___v51;
              RAST._IExpr _out31;
              DCOMP._IOwnership _out32;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out33;
              (this).GenExpr(_1354_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out31, out _out32, out _out33);
              _1355_expr = _out31;
              _1356___v50 = _out32;
              _1357___v51 = _out33;
              _1349_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1349_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1353_fieldRustName, _1355_expr)));
            }
          }
        }
        if (unmatched67) {
          unmatched67 = false;
          {
            RAST._IExpr _1358_default;
            _1358_default = RAST.__default.std__Default__default;
            if ((_1352_fieldType).IsObjectOrPointer()) {
              _1358_default = (_1352_fieldType).ToNullExpr();
            }
            _1349_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1349_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1353_fieldRustName, _1358_default)));
          }
        }
      }
      BigInteger _hi9 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1359_typeParamI = BigInteger.Zero; _1359_typeParamI < _hi9; _1359_typeParamI++) {
        DAST._IType _1360_typeArg;
        RAST._ITypeParamDecl _1361_typeParam;
        DAST._IType _out34;
        RAST._ITypeParamDecl _out35;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1359_typeParamI), out _out34, out _out35);
        _1360_typeArg = _out34;
        _1361_typeParam = _out35;
        RAST._IType _1362_rTypeArg;
        RAST._IType _out36;
        _out36 = (this).GenType(_1360_typeArg, DCOMP.GenTypeContext.@default());
        _1362_rTypeArg = _out36;
        _1348_fields = Dafny.Sequence<RAST._IField>.Concat(_1348_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1359_typeParamI)), RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1362_rTypeArg))))));
        _1349_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1349_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1359_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      DCOMP._IExternAttribute _1363_extern;
      _1363_extern = DCOMP.__default.ExtractExtern((c).dtor_attributes, (c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _1364_className = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((_1363_extern).is_SimpleExtern) {
        _1364_className = (_1363_extern).dtor_overrideName;
      } else {
        _1364_className = DCOMP.__default.escapeName((c).dtor_name);
        if ((_1363_extern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multi-argument externs not supported for classes yet"));
        }
      }
      RAST._IStruct _1365_struct;
      _1365_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1364_className, _1345_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1348_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_1363_extern).is_NoExtern) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1365_struct)));
      }
      Dafny.ISequence<RAST._IImplMember> _1366_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1367_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out37;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out38;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1343_typeParamsSeq, out _out37, out _out38);
      _1366_implBody = _out37;
      _1367_traitBodies = _out38;
      if (((_1363_extern).is_NoExtern) && (!(_1364_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default")))) {
        _1366_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.__default.SelfOwned)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel((this).allocate)).AsExpr()).ApplyType1(RAST.__default.SelfOwned)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1366_implBody);
      }
      RAST._IType _1368_selfTypeForImpl = RAST.Type.Default();
      if (((_1363_extern).is_NoExtern) || ((_1363_extern).is_UnsupportedExtern)) {
        _1368_selfTypeForImpl = RAST.Type.create_TIdentifier(_1364_className);
      } else if ((_1363_extern).is_AdvancedExtern) {
        _1368_selfTypeForImpl = (((RAST.__default.crate).MSel((_1363_extern).dtor_enclosingModule)).MSel((_1363_extern).dtor_overrideName)).AsType();
      } else if ((_1363_extern).is_SimpleExtern) {
        _1368_selfTypeForImpl = RAST.Type.create_TIdentifier((_1363_extern).dtor_overrideName);
      }
      if ((new BigInteger((_1366_implBody).Count)).Sign == 1) {
        RAST._IImpl _1369_i;
        _1369_i = RAST.Impl.create_Impl(_1345_rTypeParamsDecls, RAST.Type.create_TypeApp(_1368_selfTypeForImpl, _1344_rTypeParams), _1346_whereConstraints, _1366_implBody);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1369_i)));
      }
      RAST._IType _1370_genSelfPath;
      RAST._IType _out39;
      _out39 = DCOMP.COMP.GenPathType(path);
      _1370_genSelfPath = _out39;
      if (!(_1364_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1345_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(RAST.__default.AnyTrait))), RAST.Type.create_TypeApp(_1370_genSelfPath, _1344_rTypeParams), _1346_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(RAST.__default.AnyTrait)))))))));
      }
      Dafny.ISequence<DAST._IType> _1371_superClasses;
      _1371_superClasses = (((_1364_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) ? (Dafny.Sequence<DAST._IType>.FromElements()) : ((c).dtor_superClasses));
      BigInteger _hi10 = new BigInteger((_1371_superClasses).Count);
      for (BigInteger _1372_i = BigInteger.Zero; _1372_i < _hi10; _1372_i++) {
        DAST._IType _1373_superClass;
        _1373_superClass = (_1371_superClasses).Select(_1372_i);
        DAST._IType _source68 = _1373_superClass;
        bool unmatched68 = true;
        if (unmatched68) {
          if (_source68.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source68.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1374_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1375_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1376_properMethods = resolved0.dtor_properMethods;
              unmatched68 = false;
              {
                RAST._IType _1377_pathStr;
                RAST._IType _out40;
                _out40 = DCOMP.COMP.GenPathType(_1374_traitPath);
                _1377_pathStr = _out40;
                Dafny.ISequence<RAST._IType> _1378_typeArgs;
                Dafny.ISequence<RAST._IType> _out41;
                _out41 = (this).GenTypeArgs(_1375_typeArgs, DCOMP.GenTypeContext.@default());
                _1378_typeArgs = _out41;
                Dafny.ISequence<RAST._IImplMember> _1379_body;
                _1379_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1367_traitBodies).Contains(_1374_traitPath)) {
                  _1379_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1367_traitBodies,_1374_traitPath);
                }
                RAST._IType _1380_traitType;
                _1380_traitType = RAST.Type.create_TypeApp(_1377_pathStr, _1378_typeArgs);
                if (!((_1363_extern).is_NoExtern)) {
                  if (((new BigInteger((_1379_body).Count)).Sign == 0) && ((new BigInteger((_1376_properMethods).Count)).Sign != 0)) {
                    goto continue_0;
                  }
                  if ((new BigInteger((_1379_body).Count)) != (new BigInteger((_1376_properMethods).Count))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: In the class "), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(path, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1381_s) => {
  return ((_1381_s));
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", some proper methods of ")), (_1380_traitType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" are marked {:extern} and some are not.")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" For the Rust compiler, please make all methods (")), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_1376_properMethods, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1382_s) => {
  return (_1382_s);
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")  bodiless and mark as {:extern} and implement them in a Rust file, ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("or mark none of them as {:extern} and implement them in Dafny. ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.")));
                  }
                }
                RAST._IModDecl _1383_x;
                _1383_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1345_rTypeParamsDecls, _1380_traitType, RAST.Type.create_TypeApp(_1370_genSelfPath, _1344_rTypeParams), _1346_whereConstraints, _1379_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1383_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1345_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1380_traitType))), RAST.Type.create_TypeApp(_1370_genSelfPath, _1344_rTypeParams), _1346_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1380_traitType)))))))));
              }
            }
          }
        }
        if (unmatched68) {
          unmatched68 = false;
        }
      continue_0: ;
      }
    after_0: ;
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1384_typeParamsSeq;
      _1384_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1385_typeParamDecls;
      _1385_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1386_typeParams;
      _1386_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi11 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1387_tpI = BigInteger.Zero; _1387_tpI < _hi11; _1387_tpI++) {
          DAST._ITypeArgDecl _1388_tp;
          _1388_tp = ((t).dtor_typeParams).Select(_1387_tpI);
          DAST._IType _1389_typeArg;
          RAST._ITypeParamDecl _1390_typeParamDecl;
          DAST._IType _out42;
          RAST._ITypeParamDecl _out43;
          (this).GenTypeParam(_1388_tp, out _out42, out _out43);
          _1389_typeArg = _out42;
          _1390_typeParamDecl = _out43;
          _1384_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1384_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1389_typeArg));
          _1385_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1385_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1390_typeParamDecl));
          RAST._IType _1391_typeParam;
          RAST._IType _out44;
          _out44 = (this).GenType(_1389_typeArg, DCOMP.GenTypeContext.@default());
          _1391_typeParam = _out44;
          _1386_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1386_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1391_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1392_fullPath;
      _1392_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1393_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1394___v55;
      Dafny.ISequence<RAST._IImplMember> _out45;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out46;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1392_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1384_typeParamsSeq, out _out45, out _out46);
      _1393_implBody = _out45;
      _1394___v55 = _out46;
      Dafny.ISequence<RAST._IType> _1395_parents;
      _1395_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi12 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1396_i = BigInteger.Zero; _1396_i < _hi12; _1396_i++) {
        RAST._IType _1397_tpe;
        RAST._IType _out47;
        _out47 = (this).GenType(((t).dtor_parents).Select(_1396_i), DCOMP.GenTypeContext.ForTraitParents());
        _1397_tpe = _out47;
        _1395_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1395_parents, Dafny.Sequence<RAST._IType>.FromElements(_1397_tpe)), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply1(RAST.Type.create_DynType(_1397_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1385_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1386_typeParams), _1395_parents, _1393_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1398_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1399_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1400_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1401_whereConstraints;
      Dafny.ISequence<DAST._IType> _out48;
      Dafny.ISequence<RAST._IType> _out49;
      Dafny.ISequence<RAST._ITypeParamDecl> _out50;
      Dafny.ISequence<Dafny.Rune> _out51;
      (this).GenTypeParameters((c).dtor_typeParams, out _out48, out _out49, out _out50, out _out51);
      _1398_typeParamsSeq = _out48;
      _1399_rTypeParams = _out49;
      _1400_rTypeParamsDecls = _out50;
      _1401_whereConstraints = _out51;
      Dafny.ISequence<Dafny.Rune> _1402_constrainedTypeParams;
      _1402_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1400_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1403_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source69 = DCOMP.COMP.NewtypeRangeToRustType((c).dtor_range);
      bool unmatched69 = true;
      if (unmatched69) {
        if (_source69.is_Some) {
          RAST._IType _1404_v = _source69.dtor_value;
          unmatched69 = false;
          _1403_underlyingType = _1404_v;
        }
      }
      if (unmatched69) {
        unmatched69 = false;
        RAST._IType _out52;
        _out52 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1403_underlyingType = _out52;
      }
      DAST._IType _1405_resultingType;
      _1405_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1406_newtypeName;
      _1406_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1406_newtypeName, _1400_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1403_underlyingType))))));
      RAST._IExpr _1407_fnBody;
      _1407_fnBody = RAST.Expr.create_Identifier(_1406_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source70 = (c).dtor_witnessExpr;
      bool unmatched70 = true;
      if (unmatched70) {
        if (_source70.is_Some) {
          DAST._IExpression _1408_e = _source70.dtor_value;
          unmatched70 = false;
          {
            DAST._IExpression _1409_e;
            _1409_e = ((object.Equals((c).dtor_base, _1405_resultingType)) ? (_1408_e) : (DAST.Expression.create_Convert(_1408_e, (c).dtor_base, _1405_resultingType)));
            RAST._IExpr _1410_eStr;
            DCOMP._IOwnership _1411___v56;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1412___v57;
            RAST._IExpr _out53;
            DCOMP._IOwnership _out54;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out55;
            (this).GenExpr(_1409_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out53, out _out54, out _out55);
            _1410_eStr = _out53;
            _1411___v56 = _out54;
            _1412___v57 = _out55;
            _1407_fnBody = (_1407_fnBody).Apply1(_1410_eStr);
          }
        }
      }
      if (unmatched70) {
        unmatched70 = false;
        {
          _1407_fnBody = (_1407_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1413_body;
      _1413_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1407_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source71 = (c).dtor_constraint;
      bool unmatched71 = true;
      if (unmatched71) {
        if (_source71.is_None) {
          unmatched71 = false;
        }
      }
      if (unmatched71) {
        DAST._INewtypeConstraint value8 = _source71.dtor_value;
        DAST._IFormal _1414_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1415_constraintStmts = value8.dtor_constraintStmts;
        unmatched71 = false;
        RAST._IExpr _1416_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1417___v58;
        DCOMP._IEnvironment _1418_newEnv;
        RAST._IExpr _out56;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out57;
        DCOMP._IEnvironment _out58;
        (this).GenStmts(_1415_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out56, out _out57, out _out58);
        _1416_rStmts = _out56;
        _1417___v58 = _out57;
        _1418_newEnv = _out58;
        Dafny.ISequence<RAST._IFormal> _1419_rFormals;
        Dafny.ISequence<RAST._IFormal> _out59;
        _out59 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1414_formal), false);
        _1419_rFormals = _out59;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1400_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1406_newtypeName), _1399_rTypeParams), _1401_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1419_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1416_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1400_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1406_newtypeName), _1399_rTypeParams), _1401_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1413_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1400_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1406_newtypeName), _1399_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1400_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1406_newtypeName), _1399_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1403_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(((RAST.Path.create_Self()).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))).AsType())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1420_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1421_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1422_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1423_whereConstraints;
      Dafny.ISequence<DAST._IType> _out60;
      Dafny.ISequence<RAST._IType> _out61;
      Dafny.ISequence<RAST._ITypeParamDecl> _out62;
      Dafny.ISequence<Dafny.Rune> _out63;
      (this).GenTypeParameters((c).dtor_typeParams, out _out60, out _out61, out _out62, out _out63);
      _1420_typeParamsSeq = _out60;
      _1421_rTypeParams = _out61;
      _1422_rTypeParamsDecls = _out62;
      _1423_whereConstraints = _out63;
      Dafny.ISequence<Dafny.Rune> _1424_synonymTypeName;
      _1424_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1425_resultingType;
      RAST._IType _out64;
      _out64 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1425_resultingType = _out64;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1424_synonymTypeName, _1422_rTypeParamsDecls, _1425_resultingType)));
      Dafny.ISequence<RAST._ITypeParamDecl> _1426_defaultConstrainedTypeParams;
      _1426_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1422_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Std.Wrappers._IOption<DAST._IExpression> _source72 = (c).dtor_witnessExpr;
      bool unmatched72 = true;
      if (unmatched72) {
        if (_source72.is_Some) {
          DAST._IExpression _1427_e = _source72.dtor_value;
          unmatched72 = false;
          {
            RAST._IExpr _1428_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1429___v59;
            DCOMP._IEnvironment _1430_newEnv;
            RAST._IExpr _out65;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out66;
            DCOMP._IEnvironment _out67;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out65, out _out66, out _out67);
            _1428_rStmts = _out65;
            _1429___v59 = _out66;
            _1430_newEnv = _out67;
            RAST._IExpr _1431_rExpr;
            DCOMP._IOwnership _1432___v60;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1433___v61;
            RAST._IExpr _out68;
            DCOMP._IOwnership _out69;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out70;
            (this).GenExpr(_1427_e, DCOMP.SelfInfo.create_NoSelf(), _1430_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out68, out _out69, out _out70);
            _1431_rExpr = _out68;
            _1432___v60 = _out69;
            _1433___v61 = _out70;
            Dafny.ISequence<Dafny.Rune> _1434_constantName;
            _1434_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1434_constantName, _1426_defaultConstrainedTypeParams, Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1425_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1428_rStmts).Then(_1431_rExpr)))))));
          }
        }
      }
      if (unmatched72) {
        unmatched72 = false;
      }
      return s;
    }
    public bool TypeIsEq(DAST._IType t) {
      DAST._IType _source73 = t;
      bool unmatched73 = true;
      if (unmatched73) {
        if (_source73.is_UserDefined) {
          unmatched73 = false;
          return true;
        }
      }
      if (unmatched73) {
        if (_source73.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1435_ts = _source73.dtor_Tuple_a0;
          unmatched73 = false;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1436_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1436_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1437_t = (DAST._IType)_forall_var_5;
            return !((_1436_ts).Contains(_1437_t)) || ((this).TypeIsEq(_1437_t));
          }))))(_1435_ts);
        }
      }
      if (unmatched73) {
        if (_source73.is_Array) {
          DAST._IType _1438_t = _source73.dtor_element;
          unmatched73 = false;
          return (this).TypeIsEq(_1438_t);
        }
      }
      if (unmatched73) {
        if (_source73.is_Seq) {
          DAST._IType _1439_t = _source73.dtor_element;
          unmatched73 = false;
          return (this).TypeIsEq(_1439_t);
        }
      }
      if (unmatched73) {
        if (_source73.is_Set) {
          DAST._IType _1440_t = _source73.dtor_element;
          unmatched73 = false;
          return (this).TypeIsEq(_1440_t);
        }
      }
      if (unmatched73) {
        if (_source73.is_Multiset) {
          DAST._IType _1441_t = _source73.dtor_element;
          unmatched73 = false;
          return (this).TypeIsEq(_1441_t);
        }
      }
      if (unmatched73) {
        if (_source73.is_Map) {
          DAST._IType _1442_k = _source73.dtor_key;
          DAST._IType _1443_v = _source73.dtor_value;
          unmatched73 = false;
          return ((this).TypeIsEq(_1442_k)) && ((this).TypeIsEq(_1443_v));
        }
      }
      if (unmatched73) {
        if (_source73.is_SetBuilder) {
          DAST._IType _1444_t = _source73.dtor_element;
          unmatched73 = false;
          return (this).TypeIsEq(_1444_t);
        }
      }
      if (unmatched73) {
        if (_source73.is_MapBuilder) {
          DAST._IType _1445_k = _source73.dtor_key;
          DAST._IType _1446_v = _source73.dtor_value;
          unmatched73 = false;
          return ((this).TypeIsEq(_1445_k)) && ((this).TypeIsEq(_1446_v));
        }
      }
      if (unmatched73) {
        if (_source73.is_Arrow) {
          unmatched73 = false;
          return false;
        }
      }
      if (unmatched73) {
        if (_source73.is_Primitive) {
          unmatched73 = false;
          return true;
        }
      }
      if (unmatched73) {
        if (_source73.is_Passthrough) {
          unmatched73 = false;
          return true;
        }
      }
      if (unmatched73) {
        if (_source73.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _1447_i = _source73.dtor_TypeArg_a0;
          unmatched73 = false;
          return true;
        }
      }
      if (unmatched73) {
        unmatched73 = false;
        return true;
      }
      throw new System.Exception("unexpected control point");
    }
    public bool DatatypeIsEq(DAST._IDatatype c) {
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1448_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1448_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1449_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1449_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1450_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1448_c).dtor_ctors).Contains(_1449_ctor)) && (((_1449_ctor).dtor_args).Contains(_1450_arg))) || ((this).TypeIsEq(((_1450_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1451_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1452_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1453_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1454_whereConstraints;
      Dafny.ISequence<DAST._IType> _out71;
      Dafny.ISequence<RAST._IType> _out72;
      Dafny.ISequence<RAST._ITypeParamDecl> _out73;
      Dafny.ISequence<Dafny.Rune> _out74;
      (this).GenTypeParameters((c).dtor_typeParams, out _out71, out _out72, out _out73, out _out74);
      _1451_typeParamsSeq = _out71;
      _1452_rTypeParams = _out72;
      _1453_rTypeParamsDecls = _out73;
      _1454_whereConstraints = _out74;
      Dafny.ISequence<Dafny.Rune> _1455_datatypeName;
      _1455_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1456_ctors;
      _1456_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _1457_variances;
      _1457_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_1458_typeParamDecl) => {
        return (_1458_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1459_i = BigInteger.Zero; _1459_i < _hi13; _1459_i++) {
        DAST._IDatatypeCtor _1460_ctor;
        _1460_ctor = ((c).dtor_ctors).Select(_1459_i);
        Dafny.ISequence<RAST._IField> _1461_ctorArgs;
        _1461_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1462_isNumeric;
        _1462_isNumeric = false;
        BigInteger _hi14 = new BigInteger(((_1460_ctor).dtor_args).Count);
        for (BigInteger _1463_j = BigInteger.Zero; _1463_j < _hi14; _1463_j++) {
          DAST._IDatatypeDtor _1464_dtor;
          _1464_dtor = ((_1460_ctor).dtor_args).Select(_1463_j);
          RAST._IType _1465_formalType;
          RAST._IType _out75;
          _out75 = (this).GenType(((_1464_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1465_formalType = _out75;
          Dafny.ISequence<Dafny.Rune> _1466_formalName;
          _1466_formalName = DCOMP.__default.escapeVar(((_1464_dtor).dtor_formal).dtor_name);
          if (((_1463_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1466_formalName))) {
            _1462_isNumeric = true;
          }
          if ((((_1463_j).Sign != 0) && (_1462_isNumeric)) && (!(Std.Strings.__default.OfNat(_1463_j)).Equals(_1466_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1466_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1463_j)));
            _1462_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1461_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1461_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1466_formalName, RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1465_formalType))))));
          } else {
            _1461_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1461_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1466_formalName, _1465_formalType))));
          }
        }
        RAST._IFields _1467_namedFields;
        _1467_namedFields = RAST.Fields.create_NamedFields(_1461_ctorArgs);
        if (_1462_isNumeric) {
          _1467_namedFields = (_1467_namedFields).ToNamelessFields();
        }
        _1456_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1456_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1460_ctor).dtor_name), _1467_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1468_selfPath;
      _1468_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1469_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1470_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out76;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out77;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1468_selfPath, _1451_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1457_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1451_typeParamsSeq, out _out76, out _out77);
      _1469_implBodyRaw = _out76;
      _1470_traitBodies = _out77;
      Dafny.ISequence<RAST._IImplMember> _1471_implBody;
      _1471_implBody = _1469_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1472_emittedFields;
      _1472_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi15 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1473_i = BigInteger.Zero; _1473_i < _hi15; _1473_i++) {
        DAST._IDatatypeCtor _1474_ctor;
        _1474_ctor = ((c).dtor_ctors).Select(_1473_i);
        BigInteger _hi16 = new BigInteger(((_1474_ctor).dtor_args).Count);
        for (BigInteger _1475_j = BigInteger.Zero; _1475_j < _hi16; _1475_j++) {
          DAST._IDatatypeDtor _1476_dtor;
          _1476_dtor = ((_1474_ctor).dtor_args).Select(_1475_j);
          Dafny.ISequence<Dafny.Rune> _1477_callName;
          _1477_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1476_dtor).dtor_callName, DCOMP.__default.escapeVar(((_1476_dtor).dtor_formal).dtor_name));
          if (!((_1472_emittedFields).Contains(_1477_callName))) {
            _1472_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1472_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1477_callName));
            RAST._IType _1478_formalType;
            RAST._IType _out78;
            _out78 = (this).GenType(((_1476_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1478_formalType = _out78;
            Dafny.ISequence<RAST._IMatchCase> _1479_cases;
            _1479_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi17 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1480_k = BigInteger.Zero; _1480_k < _hi17; _1480_k++) {
              DAST._IDatatypeCtor _1481_ctor2;
              _1481_ctor2 = ((c).dtor_ctors).Select(_1480_k);
              Dafny.ISequence<Dafny.Rune> _1482_pattern;
              _1482_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1455_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1481_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1483_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1484_hasMatchingField;
              _1484_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1485_patternInner;
              _1485_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1486_isNumeric;
              _1486_isNumeric = false;
              BigInteger _hi18 = new BigInteger(((_1481_ctor2).dtor_args).Count);
              for (BigInteger _1487_l = BigInteger.Zero; _1487_l < _hi18; _1487_l++) {
                DAST._IDatatypeDtor _1488_dtor2;
                _1488_dtor2 = ((_1481_ctor2).dtor_args).Select(_1487_l);
                Dafny.ISequence<Dafny.Rune> _1489_patternName;
                _1489_patternName = DCOMP.__default.escapeVar(((_1488_dtor2).dtor_formal).dtor_name);
                if (((_1487_l).Sign == 0) && ((_1489_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1486_isNumeric = true;
                }
                if (_1486_isNumeric) {
                  _1489_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1488_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1487_l)));
                }
                if (object.Equals(((_1476_dtor).dtor_formal).dtor_name, ((_1488_dtor2).dtor_formal).dtor_name)) {
                  _1484_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1489_patternName);
                }
                _1485_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1485_patternInner, _1489_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1486_isNumeric) {
                _1482_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1482_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1485_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1482_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1482_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1485_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1484_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1483_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1484_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1483_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1484_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1483_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _1490_ctorMatch;
              _1490_ctorMatch = RAST.MatchCase.create(_1482_pattern, RAST.Expr.create_RawExpr(_1483_rhs));
              _1479_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1479_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1490_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1479_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1479_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1455_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _1491_methodBody;
            _1491_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1479_cases);
            _1471_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1471_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1477_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1478_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1491_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1492_coerceTypes;
      _1492_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1493_rCoerceTypeParams;
      _1493_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1494_coerceArguments;
      _1494_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1495_coerceMap;
      _1495_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1496_rCoerceMap;
      _1496_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1497_coerceMapToArg;
      _1497_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1498_types;
        _1498_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi19 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1499_typeI = BigInteger.Zero; _1499_typeI < _hi19; _1499_typeI++) {
          DAST._ITypeArgDecl _1500_typeParam;
          _1500_typeParam = ((c).dtor_typeParams).Select(_1499_typeI);
          DAST._IType _1501_typeArg;
          RAST._ITypeParamDecl _1502_rTypeParamDecl;
          DAST._IType _out79;
          RAST._ITypeParamDecl _out80;
          (this).GenTypeParam(_1500_typeParam, out _out79, out _out80);
          _1501_typeArg = _out79;
          _1502_rTypeParamDecl = _out80;
          RAST._IType _1503_rTypeArg;
          RAST._IType _out81;
          _out81 = (this).GenType(_1501_typeArg, DCOMP.GenTypeContext.@default());
          _1503_rTypeArg = _out81;
          _1498_types = Dafny.Sequence<RAST._IType>.Concat(_1498_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1503_rTypeArg))));
          if (((_1499_typeI) < (new BigInteger((_1457_variances).Count))) && (((_1457_variances).Select(_1499_typeI)).is_Nonvariant)) {
            _1492_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1492_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1503_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1504_coerceTypeParam;
          _1504_coerceTypeParam = Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_1500_typeParam, _pat_let20_0 => Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_pat_let20_0, _1505_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1499_typeI)), _pat_let21_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(_pat_let21_0, _1506_dt__update_hname_h0 => DAST.TypeArgDecl.create(_1506_dt__update_hname_h0, (_1505_dt__update__tmp_h0).dtor_bounds, (_1505_dt__update__tmp_h0).dtor_variance)))));
          DAST._IType _1507_coerceTypeArg;
          RAST._ITypeParamDecl _1508_rCoerceTypeParamDecl;
          DAST._IType _out82;
          RAST._ITypeParamDecl _out83;
          (this).GenTypeParam(_1504_coerceTypeParam, out _out82, out _out83);
          _1507_coerceTypeArg = _out82;
          _1508_rCoerceTypeParamDecl = _out83;
          _1495_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1495_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1501_typeArg, _1507_coerceTypeArg)));
          RAST._IType _1509_rCoerceType;
          RAST._IType _out84;
          _out84 = (this).GenType(_1507_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1509_rCoerceType = _out84;
          _1496_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1496_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1503_rTypeArg, _1509_rCoerceType)));
          _1492_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1492_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1509_rCoerceType));
          _1493_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1493_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1508_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1510_coerceFormal;
          _1510_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1499_typeI));
          _1497_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1497_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1503_rTypeArg, _1509_rCoerceType), (RAST.Expr.create_Identifier(_1510_coerceFormal)).Clone())));
          _1494_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1494_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1510_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1503_rTypeArg), _1509_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        _1456_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1456_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1511_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1511_tpe);
})), _1498_types)))));
      }
      bool _1512_cIsEq;
      _1512_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1512_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1455_datatypeName, _1453_rTypeParamsDecls, _1456_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1453_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1455_datatypeName), _1452_rTypeParams), _1454_whereConstraints, _1471_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1513_printImplBodyCases;
      _1513_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1514_hashImplBodyCases;
      _1514_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1515_coerceImplBodyCases;
      _1515_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi20 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1516_i = BigInteger.Zero; _1516_i < _hi20; _1516_i++) {
        DAST._IDatatypeCtor _1517_ctor;
        _1517_ctor = ((c).dtor_ctors).Select(_1516_i);
        Dafny.ISequence<Dafny.Rune> _1518_ctorMatch;
        _1518_ctorMatch = DCOMP.__default.escapeName((_1517_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1519_modulePrefix;
        _1519_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1520_ctorName;
        _1520_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1519_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1517_ctor).dtor_name));
        if (((new BigInteger((_1520_ctorName).Count)) >= (new BigInteger(13))) && (((_1520_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1520_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1521_printRhs;
        _1521_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1520_ctorName), (((_1517_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1522_hashRhs;
        _1522_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1523_coerceRhsArgs;
        _1523_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1524_isNumeric;
        _1524_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1525_ctorMatchInner;
        _1525_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi21 = new BigInteger(((_1517_ctor).dtor_args).Count);
        for (BigInteger _1526_j = BigInteger.Zero; _1526_j < _hi21; _1526_j++) {
          DAST._IDatatypeDtor _1527_dtor;
          _1527_dtor = ((_1517_ctor).dtor_args).Select(_1526_j);
          Dafny.ISequence<Dafny.Rune> _1528_patternName;
          _1528_patternName = DCOMP.__default.escapeVar(((_1527_dtor).dtor_formal).dtor_name);
          DAST._IType _1529_formalType;
          _1529_formalType = ((_1527_dtor).dtor_formal).dtor_typ;
          if (((_1526_j).Sign == 0) && ((_1528_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1524_isNumeric = true;
          }
          if (_1524_isNumeric) {
            _1528_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1527_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1526_j)));
          }
          _1522_hashRhs = (((_1529_formalType).is_Arrow) ? ((_1522_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))) : ((_1522_hashRhs).Then((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1528_patternName), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state")))))));
          _1525_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1525_ctorMatchInner, _1528_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1526_j).Sign == 1) {
            _1521_printRhs = (_1521_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1521_printRhs = (_1521_printRhs).Then(RAST.Expr.create_RawExpr((((_1529_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1528_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1530_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1531_formalTpe;
          RAST._IType _out85;
          _out85 = (this).GenType(_1529_formalType, DCOMP.GenTypeContext.@default());
          _1531_formalTpe = _out85;
          DAST._IType _1532_newFormalType;
          _1532_newFormalType = (_1529_formalType).Replace(_1495_coerceMap);
          RAST._IType _1533_newFormalTpe;
          _1533_newFormalTpe = (_1531_formalTpe).ReplaceMap(_1496_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1534_upcastConverter;
          _1534_upcastConverter = (this).UpcastConversionLambda(_1529_formalType, _1531_formalTpe, _1532_newFormalType, _1533_newFormalTpe, _1497_coerceMapToArg);
          if ((_1534_upcastConverter).is_Success) {
            RAST._IExpr _1535_coercionFunction;
            _1535_coercionFunction = (_1534_upcastConverter).dtor_value;
            _1530_coerceRhsArg = (_1535_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1528_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1526_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1455_datatypeName));
            _1530_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1523_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1523_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1528_patternName, _1530_coerceRhsArg)));
        }
        RAST._IExpr _1536_coerceRhs;
        _1536_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1455_datatypeName)).FSel(DCOMP.__default.escapeName((_1517_ctor).dtor_name)), _1523_coerceRhsArgs);
        if (_1524_isNumeric) {
          _1518_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1518_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1525_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1518_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1518_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1525_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1517_ctor).dtor_hasAnyArgs) {
          _1521_printRhs = (_1521_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1521_printRhs = (_1521_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1513_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1513_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1455_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1518_ctorMatch), RAST.Expr.create_Block(_1521_printRhs))));
        _1514_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1514_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1455_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1518_ctorMatch), RAST.Expr.create_Block(_1522_hashRhs))));
        _1515_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1515_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1455_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1518_ctorMatch), RAST.Expr.create_Block(_1536_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1537_extraCases;
        _1537_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1455_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _1513_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1513_printImplBodyCases, _1537_extraCases);
        _1514_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1514_hashImplBodyCases, _1537_extraCases);
        _1515_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1515_coerceImplBodyCases, _1537_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1538_defaultConstrainedTypeParams;
      _1538_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1453_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1539_rTypeParamsDeclsWithEq;
      _1539_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1453_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1540_rTypeParamsDeclsWithHash;
      _1540_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1453_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1541_printImplBody;
      _1541_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1513_printImplBodyCases);
      RAST._IExpr _1542_hashImplBody;
      _1542_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1514_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1453_rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug"))).AsType(), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1455_datatypeName), _1452_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType()))), Std.Wrappers.Option<RAST._IType>.create_Some((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Result"))).AsType()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1453_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1455_datatypeName), _1452_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType())), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1541_printImplBody))))))));
      if ((new BigInteger((_1493_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1543_coerceImplBody;
        _1543_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1515_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1453_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1455_datatypeName), _1452_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1493_rCoerceTypeParams, _1494_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1455_datatypeName), _1452_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1455_datatypeName), _1492_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.__default.SelfOwned)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1455_datatypeName), _1492_coerceTypes)), _1543_coerceImplBody))))))))));
      }
      if (_1512_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1539_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1455_datatypeName), _1452_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1540_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1455_datatypeName), _1452_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))).AsType()))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1542_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1544_structName;
        _1544_structName = (RAST.Expr.create_Identifier(_1455_datatypeName)).FSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1545_structAssignments;
        _1545_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi22 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1546_i = BigInteger.Zero; _1546_i < _hi22; _1546_i++) {
          DAST._IDatatypeDtor _1547_dtor;
          _1547_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1546_i);
          _1545_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1545_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(((_1547_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1548_defaultConstrainedTypeParams;
        _1548_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1453_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1549_fullType;
        _1549_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1455_datatypeName), _1452_rTypeParams);
        if (_1512_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1548_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1549_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1549_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1544_structName, _1545_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1453_rTypeParamsDecls, ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).AsType()).Apply1(_1549_fullType), RAST.Type.create_Borrowed(_1549_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
      }
      return s;
    }
    public static RAST._IPath GenPath(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p, bool escape)
    {
      RAST._IPath r = RAST.Path.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        r = RAST.Path.create_Self();
        return r;
      } else {
        r = ((((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))) ? (RAST.Path.create_Global()) : (((((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"))) ? (RAST.__default.dafny__runtime) : (RAST.Path.create_Crate()))));
        BigInteger _hi23 = new BigInteger((p).Count);
        for (BigInteger _1550_i = BigInteger.Zero; _1550_i < _hi23; _1550_i++) {
          Dafny.ISequence<Dafny.Rune> _1551_name;
          _1551_name = ((p).Select(_1550_i));
          if (escape) {
            _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs55 = DafnyCompilerRustUtils.__default.DafnyNameToContainingPathAndName(_1551_name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1552_modules = _let_tmp_rhs55.dtor__0;
            Dafny.ISequence<Dafny.Rune> _1553_finalName = _let_tmp_rhs55.dtor__1;
            BigInteger _hi24 = new BigInteger((_1552_modules).Count);
            for (BigInteger _1554_j = BigInteger.Zero; _1554_j < _hi24; _1554_j++) {
              r = (r).MSel(DCOMP.__default.escapeName(((_1552_modules).Select(_1554_j))));
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1553_finalName));
          } else {
            r = (r).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1551_name)));
          }
        }
      }
      return r;
    }
    public static RAST._IType GenPathType(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IType t = RAST.Type.Default();
      RAST._IPath _1555_p;
      RAST._IPath _out86;
      _out86 = DCOMP.COMP.GenPath(p, true);
      _1555_p = _out86;
      t = (_1555_p).AsType();
      return t;
    }
    public static RAST._IExpr GenPathExpr(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p, bool escape)
    {
      RAST._IExpr e = RAST.Expr.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        e = RAST.__default.self;
        return e;
      }
      RAST._IPath _1556_p;
      RAST._IPath _out87;
      _out87 = DCOMP.COMP.GenPath(p, escape);
      _1556_p = _out87;
      e = (_1556_p).AsExpr();
      return e;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi25 = new BigInteger((args).Count);
      for (BigInteger _1557_i = BigInteger.Zero; _1557_i < _hi25; _1557_i++) {
        RAST._IType _1558_genTp;
        RAST._IType _out88;
        _out88 = (this).GenType((args).Select(_1557_i), genTypeContext);
        _1558_genTp = _out88;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1558_genTp));
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, DCOMP._IGenTypeContext genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source74 = c;
      bool unmatched74 = true;
      if (unmatched74) {
        if (_source74.is_UserDefined) {
          DAST._IResolvedType _1559_resolved = _source74.dtor_resolved;
          unmatched74 = false;
          {
            RAST._IType _1560_t;
            RAST._IType _out89;
            _out89 = DCOMP.COMP.GenPathType((_1559_resolved).dtor_path);
            _1560_t = _out89;
            Dafny.ISequence<RAST._IType> _1561_typeArgs;
            Dafny.ISequence<RAST._IType> _out90;
            _out90 = (this).GenTypeArgs((_1559_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let22_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let22_0, _1562_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let23_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let23_0, _1563_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1562_dt__update__tmp_h0).dtor_inBinding, (_1562_dt__update__tmp_h0).dtor_inFn, _1563_dt__update_hforTraitParents_h0))))));
            _1561_typeArgs = _out90;
            s = RAST.Type.create_TypeApp(_1560_t, _1561_typeArgs);
            DAST._IResolvedTypeBase _source75 = (_1559_resolved).dtor_kind;
            bool unmatched75 = true;
            if (unmatched75) {
              if (_source75.is_Class) {
                unmatched75 = false;
                {
                  s = (this).Object(s);
                }
              }
            }
            if (unmatched75) {
              if (_source75.is_Datatype) {
                unmatched75 = false;
                {
                  if ((this).IsRcWrapped((_1559_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched75) {
              if (_source75.is_Trait) {
                unmatched75 = false;
                {
                  if (((_1559_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = RAST.__default.AnyTrait;
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched75) {
              DAST._IType _1564_base = _source75.dtor_baseType;
              DAST._INewtypeRange _1565_range = _source75.dtor_range;
              bool _1566_erased = _source75.dtor_erase;
              unmatched75 = false;
              {
                if (_1566_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source76 = DCOMP.COMP.NewtypeRangeToRustType(_1565_range);
                  bool unmatched76 = true;
                  if (unmatched76) {
                    if (_source76.is_Some) {
                      RAST._IType _1567_v = _source76.dtor_value;
                      unmatched76 = false;
                      s = _1567_v;
                    }
                  }
                  if (unmatched76) {
                    unmatched76 = false;
                    RAST._IType _1568_underlying;
                    RAST._IType _out91;
                    _out91 = (this).GenType(_1564_base, DCOMP.GenTypeContext.@default());
                    _1568_underlying = _out91;
                    s = RAST.Type.create_TSynonym(s, _1568_underlying);
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Object) {
          unmatched74 = false;
          {
            s = RAST.__default.AnyTrait;
            if (!((genTypeContext).dtor_forTraitParents)) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1569_types = _source74.dtor_Tuple_a0;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IType> _1570_args;
            _1570_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1571_i;
            _1571_i = BigInteger.Zero;
            while ((_1571_i) < (new BigInteger((_1569_types).Count))) {
              RAST._IType _1572_generated;
              RAST._IType _out92;
              _out92 = (this).GenType((_1569_types).Select(_1571_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let24_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let24_0, _1573_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let25_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let25_0, _1574_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1573_dt__update__tmp_h1).dtor_inBinding, (_1573_dt__update__tmp_h1).dtor_inFn, _1574_dt__update_hforTraitParents_h1))))));
              _1572_generated = _out92;
              _1570_args = Dafny.Sequence<RAST._IType>.Concat(_1570_args, Dafny.Sequence<RAST._IType>.FromElements(_1572_generated));
              _1571_i = (_1571_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1569_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1570_args)) : (RAST.__default.SystemTupleType(_1570_args)));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Array) {
          DAST._IType _1575_element = _source74.dtor_element;
          BigInteger _1576_dims = _source74.dtor_dims;
          unmatched74 = false;
          {
            if ((_1576_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1577_elem;
              RAST._IType _out93;
              _out93 = (this).GenType(_1575_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let26_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let26_0, _1578_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let27_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let27_0, _1579_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1578_dt__update__tmp_h2).dtor_inBinding, (_1578_dt__update__tmp_h2).dtor_inFn, _1579_dt__update_hforTraitParents_h2))))));
              _1577_elem = _out93;
              if ((_1576_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1577_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1580_n;
                _1580_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1576_dims));
                s = (((RAST.__default.dafny__runtime).MSel(_1580_n)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1577_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Seq) {
          DAST._IType _1581_element = _source74.dtor_element;
          unmatched74 = false;
          {
            RAST._IType _1582_elem;
            RAST._IType _out94;
            _out94 = (this).GenType(_1581_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let28_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let28_0, _1583_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let29_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let29_0, _1584_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1583_dt__update__tmp_h3).dtor_inBinding, (_1583_dt__update__tmp_h3).dtor_inFn, _1584_dt__update_hforTraitParents_h3))))));
            _1582_elem = _out94;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1582_elem));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Set) {
          DAST._IType _1585_element = _source74.dtor_element;
          unmatched74 = false;
          {
            RAST._IType _1586_elem;
            RAST._IType _out95;
            _out95 = (this).GenType(_1585_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let30_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let30_0, _1587_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let31_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let31_0, _1588_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1587_dt__update__tmp_h4).dtor_inBinding, (_1587_dt__update__tmp_h4).dtor_inFn, _1588_dt__update_hforTraitParents_h4))))));
            _1586_elem = _out95;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1586_elem));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Multiset) {
          DAST._IType _1589_element = _source74.dtor_element;
          unmatched74 = false;
          {
            RAST._IType _1590_elem;
            RAST._IType _out96;
            _out96 = (this).GenType(_1589_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let32_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let32_0, _1591_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let33_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let33_0, _1592_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1591_dt__update__tmp_h5).dtor_inBinding, (_1591_dt__update__tmp_h5).dtor_inFn, _1592_dt__update_hforTraitParents_h5))))));
            _1590_elem = _out96;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1590_elem));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Map) {
          DAST._IType _1593_key = _source74.dtor_key;
          DAST._IType _1594_value = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IType _1595_keyType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1593_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let34_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let34_0, _1596_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let35_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let35_0, _1597_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1596_dt__update__tmp_h6).dtor_inBinding, (_1596_dt__update__tmp_h6).dtor_inFn, _1597_dt__update_hforTraitParents_h6))))));
            _1595_keyType = _out97;
            RAST._IType _1598_valueType;
            RAST._IType _out98;
            _out98 = (this).GenType(_1594_value, genTypeContext);
            _1598_valueType = _out98;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1595_keyType, _1598_valueType));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapBuilder) {
          DAST._IType _1599_key = _source74.dtor_key;
          DAST._IType _1600_value = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IType _1601_keyType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1599_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let36_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let36_0, _1602_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let37_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let37_0, _1603_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1602_dt__update__tmp_h7).dtor_inBinding, (_1602_dt__update__tmp_h7).dtor_inFn, _1603_dt__update_hforTraitParents_h7))))));
            _1601_keyType = _out99;
            RAST._IType _1604_valueType;
            RAST._IType _out100;
            _out100 = (this).GenType(_1600_value, genTypeContext);
            _1604_valueType = _out100;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1601_keyType, _1604_valueType));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SetBuilder) {
          DAST._IType _1605_elem = _source74.dtor_element;
          unmatched74 = false;
          {
            RAST._IType _1606_elemType;
            RAST._IType _out101;
            _out101 = (this).GenType(_1605_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let38_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let38_0, _1607_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let39_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let39_0, _1608_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1607_dt__update__tmp_h8).dtor_inBinding, (_1607_dt__update__tmp_h8).dtor_inFn, _1608_dt__update_hforTraitParents_h8))))));
            _1606_elemType = _out101;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1606_elemType));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1609_args = _source74.dtor_args;
          DAST._IType _1610_result = _source74.dtor_result;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IType> _1611_argTypes;
            _1611_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1612_i;
            _1612_i = BigInteger.Zero;
            while ((_1612_i) < (new BigInteger((_1609_args).Count))) {
              RAST._IType _1613_generated;
              RAST._IType _out102;
              _out102 = (this).GenType((_1609_args).Select(_1612_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let40_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let40_0, _1614_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let41_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let41_0, _1615_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let42_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let42_0, _1616_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1614_dt__update__tmp_h9).dtor_inBinding, _1616_dt__update_hinFn_h0, _1615_dt__update_hforTraitParents_h9))))))));
              _1613_generated = _out102;
              _1611_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1611_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1613_generated)));
              _1612_i = (_1612_i) + (BigInteger.One);
            }
            RAST._IType _1617_resultType;
            RAST._IType _out103;
            _out103 = (this).GenType(_1610_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1617_resultType = _out103;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1611_argTypes, _1617_resultType)));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source74.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1618_name = _h90;
          unmatched74 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1618_name));
        }
      }
      if (unmatched74) {
        if (_source74.is_Primitive) {
          DAST._IPrimitive _1619_p = _source74.dtor_Primitive_a0;
          unmatched74 = false;
          {
            DAST._IPrimitive _source77 = _1619_p;
            bool unmatched77 = true;
            if (unmatched77) {
              if (_source77.is_Int) {
                unmatched77 = false;
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).AsType();
              }
            }
            if (unmatched77) {
              if (_source77.is_Real) {
                unmatched77 = false;
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"))).AsType();
              }
            }
            if (unmatched77) {
              if (_source77.is_String) {
                unmatched77 = false;
                s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType()));
              }
            }
            if (unmatched77) {
              if (_source77.is_Bool) {
                unmatched77 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched77) {
              unmatched77 = false;
              s = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType();
            }
          }
        }
      }
      if (unmatched74) {
        Dafny.ISequence<Dafny.Rune> _1620_v = _source74.dtor_Passthrough_a0;
        unmatched74 = false;
        s = RAST.__default.RawType(_1620_v);
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
      for (BigInteger _1621_i = BigInteger.Zero; _1621_i < _hi26; _1621_i++) {
        DAST._IMethod _source78 = (body).Select(_1621_i);
        bool unmatched78 = true;
        if (unmatched78) {
          DAST._IMethod _1622_m = _source78;
          unmatched78 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source79 = (_1622_m).dtor_overridingPath;
            bool unmatched79 = true;
            if (unmatched79) {
              if (_source79.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1623_p = _source79.dtor_value;
                unmatched79 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1624_existing;
                  _1624_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1623_p)) {
                    _1624_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1623_p);
                  }
                  if (((new BigInteger(((_1622_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1625_genMethod;
                  RAST._IImplMember _out104;
                  _out104 = (this).GenMethod(_1622_m, true, enclosingType, enclosingTypeParams);
                  _1625_genMethod = _out104;
                  _1624_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1624_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1625_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1623_p, _1624_existing)));
                }
              }
            }
            if (unmatched79) {
              unmatched79 = false;
              {
                RAST._IImplMember _1626_generated;
                RAST._IImplMember _out105;
                _out105 = (this).GenMethod(_1622_m, forTrait, enclosingType, enclosingTypeParams);
                _1626_generated = _out105;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1626_generated));
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
      for (BigInteger _1627_i = BigInteger.Zero; _1627_i < _hi27; _1627_i++) {
        DAST._IFormal _1628_param;
        _1628_param = (@params).Select(_1627_i);
        RAST._IType _1629_paramType;
        RAST._IType _out106;
        _out106 = (this).GenType((_1628_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1629_paramType = _out106;
        if (((!((_1629_paramType).CanReadWithoutClone())) || (forLambda)) && (!((_1628_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1629_paramType = RAST.Type.create_Borrowed(_1629_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeVar((_1628_param).dtor_name), _1629_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1630_params;
      Dafny.ISequence<RAST._IFormal> _out107;
      _out107 = (this).GenParams((m).dtor_params, false);
      _1630_params = _out107;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1631_paramNames;
      _1631_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1632_paramTypes;
      _1632_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1633_paramI = BigInteger.Zero; _1633_paramI < _hi28; _1633_paramI++) {
        DAST._IFormal _1634_dafny__formal;
        _1634_dafny__formal = ((m).dtor_params).Select(_1633_paramI);
        RAST._IFormal _1635_formal;
        _1635_formal = (_1630_params).Select(_1633_paramI);
        Dafny.ISequence<Dafny.Rune> _1636_name;
        _1636_name = (_1635_formal).dtor_name;
        _1631_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1631_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1636_name));
        _1632_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1632_paramTypes, _1636_name, (_1635_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1637_fnName;
      _1637_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1638_selfIdent;
      _1638_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1639_selfId;
        _1639_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1639_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv196 = enclosingTypeParams;
        var _pat_let_tv197 = enclosingType;
        DAST._IType _1640_instanceType;
        _1640_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source80 = enclosingType;
          bool unmatched80 = true;
          if (unmatched80) {
            if (_source80.is_UserDefined) {
              DAST._IResolvedType _1641_r = _source80.dtor_resolved;
              unmatched80 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1641_r, _pat_let43_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let43_0, _1642_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv196, _pat_let44_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let44_0, _1643_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1642_dt__update__tmp_h0).dtor_path, _1643_dt__update_htypeArgs_h0, (_1642_dt__update__tmp_h0).dtor_kind, (_1642_dt__update__tmp_h0).dtor_attributes, (_1642_dt__update__tmp_h0).dtor_properMethods, (_1642_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched80) {
            unmatched80 = false;
            return _pat_let_tv197;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1644_selfFormal;
          _1644_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1630_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1644_selfFormal), _1630_params);
        } else {
          RAST._IType _1645_tpe;
          RAST._IType _out108;
          _out108 = (this).GenType(_1640_instanceType, DCOMP.GenTypeContext.@default());
          _1645_tpe = _out108;
          if ((_1639_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1645_tpe = RAST.Type.create_Borrowed(_1645_tpe);
          } else if ((_1639_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1645_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1645_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1645_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _1645_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.__default.SelfOwned));
              } else {
                _1645_tpe = RAST.Type.create_Borrowed(RAST.__default.SelfOwned);
              }
            }
          }
          _1630_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1639_selfId, _1645_tpe)), _1630_params);
        }
        _1638_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1639_selfId, _1640_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1646_retTypeArgs;
      _1646_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1647_typeI;
      _1647_typeI = BigInteger.Zero;
      while ((_1647_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1648_typeExpr;
        RAST._IType _out109;
        _out109 = (this).GenType(((m).dtor_outTypes).Select(_1647_typeI), DCOMP.GenTypeContext.@default());
        _1648_typeExpr = _out109;
        _1646_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1646_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1648_typeExpr));
        _1647_typeI = (_1647_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1649_visibility;
      _1649_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1650_typeParamsFiltered;
      _1650_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi29 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1651_typeParamI = BigInteger.Zero; _1651_typeParamI < _hi29; _1651_typeParamI++) {
        DAST._ITypeArgDecl _1652_typeParam;
        _1652_typeParam = ((m).dtor_typeParams).Select(_1651_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1652_typeParam).dtor_name)))) {
          _1650_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1650_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1652_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1653_typeParams;
      _1653_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1650_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi30 = new BigInteger((_1650_typeParamsFiltered).Count);
        for (BigInteger _1654_i = BigInteger.Zero; _1654_i < _hi30; _1654_i++) {
          DAST._IType _1655_typeArg;
          RAST._ITypeParamDecl _1656_rTypeParamDecl;
          DAST._IType _out110;
          RAST._ITypeParamDecl _out111;
          (this).GenTypeParam((_1650_typeParamsFiltered).Select(_1654_i), out _out110, out _out111);
          _1655_typeArg = _out110;
          _1656_rTypeParamDecl = _out111;
          var _pat_let_tv198 = _1656_rTypeParamDecl;
          _1656_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1656_rTypeParamDecl, _pat_let45_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let45_0, _1657_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv198).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait)), _pat_let46_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let46_0, _1658_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1657_dt__update__tmp_h1).dtor_content, _1658_dt__update_hconstraints_h0)))));
          _1653_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1653_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1656_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1659_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1660_env = DCOMP.Environment.Default();
      RAST._IExpr _1661_preBody;
      _1661_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1662_preAssignNames;
      _1662_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1663_preAssignTypes;
      _1663_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1664_earlyReturn;
        _1664_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source81 = (m).dtor_outVars;
        bool unmatched81 = true;
        if (unmatched81) {
          if (_source81.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1665_outVars = _source81.dtor_value;
            unmatched81 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1664_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi31 = new BigInteger((_1665_outVars).Count);
                for (BigInteger _1666_outI = BigInteger.Zero; _1666_outI < _hi31; _1666_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1667_outVar;
                  _1667_outVar = (_1665_outVars).Select(_1666_outI);
                  Dafny.ISequence<Dafny.Rune> _1668_outName;
                  _1668_outName = DCOMP.__default.escapeVar(_1667_outVar);
                  Dafny.ISequence<Dafny.Rune> _1669_tracker__name;
                  _1669_tracker__name = DCOMP.__default.AddAssignedPrefix(_1668_outName);
                  _1662_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1662_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1669_tracker__name));
                  _1663_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1663_preAssignTypes, _1669_tracker__name, RAST.Type.create_Bool());
                  _1661_preBody = (_1661_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1669_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1670_tupleArgs;
                _1670_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi32 = new BigInteger((_1665_outVars).Count);
                for (BigInteger _1671_outI = BigInteger.Zero; _1671_outI < _hi32; _1671_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1672_outVar;
                  _1672_outVar = (_1665_outVars).Select(_1671_outI);
                  RAST._IType _1673_outType;
                  RAST._IType _out112;
                  _out112 = (this).GenType(((m).dtor_outTypes).Select(_1671_outI), DCOMP.GenTypeContext.@default());
                  _1673_outType = _out112;
                  Dafny.ISequence<Dafny.Rune> _1674_outName;
                  _1674_outName = DCOMP.__default.escapeVar(_1672_outVar);
                  _1631_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1631_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1674_outName));
                  RAST._IType _1675_outMaybeType;
                  _1675_outMaybeType = (((_1673_outType).CanReadWithoutClone()) ? (_1673_outType) : (RAST.__default.MaybePlaceboType(_1673_outType)));
                  _1632_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1632_paramTypes, _1674_outName, _1675_outMaybeType);
                  _1670_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1670_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1674_outName));
                }
                _1664_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_1670_tupleArgs);
              }
            }
          }
        }
        if (unmatched81) {
          unmatched81 = false;
        }
        _1660_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1662_preAssignNames, _1631_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1663_preAssignTypes, _1632_paramTypes));
        RAST._IExpr _1676_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1677___v70;
        DCOMP._IEnvironment _1678___v71;
        RAST._IExpr _out113;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out114;
        DCOMP._IEnvironment _out115;
        (this).GenStmts((m).dtor_body, _1638_selfIdent, _1660_env, true, _1664_earlyReturn, out _out113, out _out114, out _out115);
        _1676_body = _out113;
        _1677___v70 = _out114;
        _1678___v71 = _out115;
        _1659_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1661_preBody).Then(_1676_body));
      } else {
        _1660_env = DCOMP.Environment.create(_1631_paramNames, _1632_paramTypes);
        _1659_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1649_visibility, RAST.Fn.create(_1637_fnName, _1653_typeParams, _1630_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1646_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1646_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1646_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1659_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1679_declarations;
      _1679_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1680_i;
      _1680_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1681_stmts;
      _1681_stmts = stmts;
      while ((_1680_i) < (new BigInteger((_1681_stmts).Count))) {
        DAST._IStatement _1682_stmt;
        _1682_stmt = (_1681_stmts).Select(_1680_i);
        DAST._IStatement _source82 = _1682_stmt;
        bool unmatched82 = true;
        if (unmatched82) {
          if (_source82.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1683_name = _source82.dtor_name;
            DAST._IType _1684_optType = _source82.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source82.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched82 = false;
              if (((_1680_i) + (BigInteger.One)) < (new BigInteger((_1681_stmts).Count))) {
                DAST._IStatement _source83 = (_1681_stmts).Select((_1680_i) + (BigInteger.One));
                bool unmatched83 = true;
                if (unmatched83) {
                  if (_source83.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source83.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> _1685_name2 = lhs0.dtor_ident;
                      DAST._IExpression _1686_rhs = _source83.dtor_value;
                      unmatched83 = false;
                      if (object.Equals(_1685_name2, _1683_name)) {
                        _1681_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1681_stmts).Subsequence(BigInteger.Zero, _1680_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1683_name, _1684_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1686_rhs)))), (_1681_stmts).Drop((_1680_i) + (new BigInteger(2))));
                        _1682_stmt = (_1681_stmts).Select(_1680_i);
                      }
                    }
                  }
                }
                if (unmatched83) {
                  unmatched83 = false;
                }
              }
            }
          }
        }
        if (unmatched82) {
          unmatched82 = false;
        }
        RAST._IExpr _1687_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1688_recIdents;
        DCOMP._IEnvironment _1689_newEnv2;
        RAST._IExpr _out116;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
        DCOMP._IEnvironment _out118;
        (this).GenStmt(_1682_stmt, selfIdent, newEnv, (isLast) && ((_1680_i) == ((new BigInteger((_1681_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out116, out _out117, out _out118);
        _1687_stmtExpr = _out116;
        _1688_recIdents = _out117;
        _1689_newEnv2 = _out118;
        newEnv = _1689_newEnv2;
        DAST._IStatement _source84 = _1682_stmt;
        bool unmatched84 = true;
        if (unmatched84) {
          if (_source84.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1690_name = _source84.dtor_name;
            unmatched84 = false;
            {
              _1679_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1679_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_1690_name)));
            }
          }
        }
        if (unmatched84) {
          unmatched84 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1688_recIdents, _1679_declarations));
        generated = (generated).Then(_1687_stmtExpr);
        _1680_i = (_1680_i) + (BigInteger.One);
        if ((_1687_stmtExpr).is_Return) {
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
      DAST._IAssignLhs _source85 = lhs;
      bool unmatched85 = true;
      if (unmatched85) {
        if (_source85.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1691_id = _source85.dtor_ident;
          unmatched85 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1692_idRust;
            _1692_idRust = DCOMP.__default.escapeVar(_1691_id);
            if (((env).IsBorrowed(_1692_idRust)) || ((env).IsBorrowedMut(_1692_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1692_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1692_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1692_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched85) {
        if (_source85.is_Select) {
          DAST._IExpression _1693_on = _source85.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1694_field = _source85.dtor_field;
          unmatched85 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1695_fieldName;
            _1695_fieldName = DCOMP.__default.escapeVar(_1694_field);
            RAST._IExpr _1696_onExpr;
            DCOMP._IOwnership _1697_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1698_recIdents;
            RAST._IExpr _out119;
            DCOMP._IOwnership _out120;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
            (this).GenExpr(_1693_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out119, out _out120, out _out121);
            _1696_onExpr = _out119;
            _1697_onOwned = _out120;
            _1698_recIdents = _out121;
            RAST._IExpr _source86 = _1696_onExpr;
            bool unmatched86 = true;
            if (unmatched86) {
              bool disjunctiveMatch12 = false;
              if (_source86.is_Call) {
                RAST._IExpr obj2 = _source86.dtor_obj;
                if (obj2.is_Select) {
                  RAST._IExpr obj3 = obj2.dtor_obj;
                  if (obj3.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name4 = obj3.dtor_name;
                    if (object.Equals(name4, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      Dafny.ISequence<Dafny.Rune> name5 = obj2.dtor_name;
                      if (object.Equals(name5, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                        disjunctiveMatch12 = true;
                      }
                    }
                  }
                }
              }
              if (_source86.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name6 = _source86.dtor_name;
                if (object.Equals(name6, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch12 = true;
                }
              }
              if (_source86.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op14 = _source86.dtor_op1;
                if (object.Equals(op14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying4 = _source86.dtor_underlying;
                  if (underlying4.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name7 = underlying4.dtor_name;
                    if (object.Equals(name7, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      disjunctiveMatch12 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch12) {
                unmatched86 = false;
                Dafny.ISequence<Dafny.Rune> _1699_isAssignedVar;
                _1699_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1695_fieldName);
                if (((newEnv).dtor_names).Contains(_1699_isAssignedVar)) {
                  generated = (((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1695_fieldName), RAST.Expr.create_Identifier(_1699_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1699_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1699_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1695_fieldName, rhs);
                }
              }
            }
            if (unmatched86) {
              unmatched86 = false;
              if (!object.Equals(_1696_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1696_onExpr = ((this).modify__macro).Apply1(_1696_onExpr);
              }
              generated = RAST.__default.AssignMember(_1696_onExpr, _1695_fieldName, rhs);
            }
            readIdents = _1698_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched85) {
        DAST._IExpression _1700_on = _source85.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1701_indices = _source85.dtor_indices;
        unmatched85 = false;
        {
          RAST._IExpr _1702_onExpr;
          DCOMP._IOwnership _1703_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1704_recIdents;
          RAST._IExpr _out122;
          DCOMP._IOwnership _out123;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
          (this).GenExpr(_1700_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out122, out _out123, out _out124);
          _1702_onExpr = _out122;
          _1703_onOwned = _out123;
          _1704_recIdents = _out124;
          readIdents = _1704_recIdents;
          _1702_onExpr = ((this).modify__macro).Apply1(_1702_onExpr);
          RAST._IExpr _1705_r;
          _1705_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1706_indicesExpr;
          _1706_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi33 = new BigInteger((_1701_indices).Count);
          for (BigInteger _1707_i = BigInteger.Zero; _1707_i < _hi33; _1707_i++) {
            RAST._IExpr _1708_idx;
            DCOMP._IOwnership _1709___v80;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1710_recIdentsIdx;
            RAST._IExpr _out125;
            DCOMP._IOwnership _out126;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out127;
            (this).GenExpr((_1701_indices).Select(_1707_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out125, out _out126, out _out127);
            _1708_idx = _out125;
            _1709___v80 = _out126;
            _1710_recIdentsIdx = _out127;
            Dafny.ISequence<Dafny.Rune> _1711_varName;
            _1711_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1707_i));
            _1706_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1706_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1711_varName)));
            _1705_r = (_1705_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1711_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1708_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1710_recIdentsIdx);
          }
          if ((new BigInteger((_1701_indices).Count)) > (BigInteger.One)) {
            _1702_onExpr = (_1702_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1712_rhs;
          _1712_rhs = rhs;
          var _pat_let_tv199 = env;
          if (((_1702_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1702_onExpr).LhsIdentifierName(), _pat_let47_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let47_0, _1713_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv199).GetType(_1713_name), _pat_let48_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let48_0, _1714_tpe => ((_1714_tpe).is_Some) && (((_1714_tpe).dtor_value).IsUninitArray())))))))) {
            _1712_rhs = RAST.__default.MaybeUninitNew(_1712_rhs);
          }
          generated = (_1705_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1702_onExpr, _1706_indicesExpr)), _1712_rhs));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source87 = stmt;
      bool unmatched87 = true;
      if (unmatched87) {
        if (_source87.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1715_fields = _source87.dtor_fields;
          unmatched87 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi34 = new BigInteger((_1715_fields).Count);
            for (BigInteger _1716_i = BigInteger.Zero; _1716_i < _hi34; _1716_i++) {
              DAST._IFormal _1717_field;
              _1717_field = (_1715_fields).Select(_1716_i);
              Dafny.ISequence<Dafny.Rune> _1718_fieldName;
              _1718_fieldName = DCOMP.__default.escapeVar((_1717_field).dtor_name);
              RAST._IType _1719_fieldTyp;
              RAST._IType _out128;
              _out128 = (this).GenType((_1717_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1719_fieldTyp = _out128;
              Dafny.ISequence<Dafny.Rune> _1720_isAssignedVar;
              _1720_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1718_fieldName);
              if (((newEnv).dtor_names).Contains(_1720_isAssignedVar)) {
                RAST._IExpr _1721_rhs;
                DCOMP._IOwnership _1722___v81;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1723___v82;
                RAST._IExpr _out129;
                DCOMP._IOwnership _out130;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1717_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out129, out _out130, out _out131);
                _1721_rhs = _out129;
                _1722___v81 = _out130;
                _1723___v82 = _out131;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1720_isAssignedVar));
                generated = (generated).Then((((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1718_fieldName), RAST.Expr.create_Identifier(_1720_isAssignedVar), _1721_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1720_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1724_name = _source87.dtor_name;
          DAST._IType _1725_typ = _source87.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source87.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1726_expression = maybeValue1.dtor_value;
            unmatched87 = false;
            {
              RAST._IType _1727_tpe;
              RAST._IType _out132;
              _out132 = (this).GenType(_1725_typ, DCOMP.GenTypeContext.InBinding());
              _1727_tpe = _out132;
              Dafny.ISequence<Dafny.Rune> _1728_varName;
              _1728_varName = DCOMP.__default.escapeVar(_1724_name);
              bool _1729_hasCopySemantics;
              _1729_hasCopySemantics = (_1727_tpe).CanReadWithoutClone();
              if (((_1726_expression).is_InitializationValue) && (!(_1729_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1728_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.MaybePlaceboPath).AsExpr()).ApplyType1(_1727_tpe)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1728_varName, RAST.__default.MaybePlaceboType(_1727_tpe));
              } else {
                RAST._IExpr _1730_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1731_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1726_expression).is_InitializationValue) && ((_1727_tpe).IsObjectOrPointer())) {
                  _1730_expr = (_1727_tpe).ToNullExpr();
                  _1731_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1732_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out133;
                  DCOMP._IOwnership _out134;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
                  (this).GenExpr(_1726_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
                  _1730_expr = _out133;
                  _1732_exprOwnership = _out134;
                  _1731_recIdents = _out135;
                }
                readIdents = _1731_recIdents;
                _1727_tpe = (((_1726_expression).is_NewUninitArray) ? ((_1727_tpe).TypeAtInitialization()) : (_1727_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1728_varName, Std.Wrappers.Option<RAST._IType>.create_Some(_1727_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1730_expr));
                newEnv = (env).AddAssigned(_1728_varName, _1727_tpe);
              }
            }
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1733_name = _source87.dtor_name;
          DAST._IType _1734_typ = _source87.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source87.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched87 = false;
            {
              DAST._IStatement _1735_newStmt;
              _1735_newStmt = DAST.Statement.create_DeclareVar(_1733_name, _1734_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1734_typ)));
              RAST._IExpr _out136;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
              DCOMP._IEnvironment _out138;
              (this).GenStmt(_1735_newStmt, selfIdent, env, isLast, earlyReturn, out _out136, out _out137, out _out138);
              generated = _out136;
              readIdents = _out137;
              newEnv = _out138;
            }
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Assign) {
          DAST._IAssignLhs _1736_lhs = _source87.dtor_lhs;
          DAST._IExpression _1737_expression = _source87.dtor_value;
          unmatched87 = false;
          {
            RAST._IExpr _1738_exprGen;
            DCOMP._IOwnership _1739___v83;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1740_exprIdents;
            RAST._IExpr _out139;
            DCOMP._IOwnership _out140;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
            (this).GenExpr(_1737_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out139, out _out140, out _out141);
            _1738_exprGen = _out139;
            _1739___v83 = _out140;
            _1740_exprIdents = _out141;
            if ((_1736_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1741_rustId;
              _1741_rustId = DCOMP.__default.escapeVar((_1736_lhs).dtor_ident);
              Std.Wrappers._IOption<RAST._IType> _1742_tpe;
              _1742_tpe = (env).GetType(_1741_rustId);
              if (((_1742_tpe).is_Some) && ((((_1742_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1738_exprGen = RAST.__default.MaybePlacebo(_1738_exprGen);
              }
            }
            if (((_1736_lhs).is_Index) && (((_1736_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1743_rustId;
              _1743_rustId = DCOMP.__default.escapeVar(((_1736_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1744_tpe;
              _1744_tpe = (env).GetType(_1743_rustId);
              if (((_1744_tpe).is_Some) && ((((_1744_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1738_exprGen = RAST.__default.MaybeUninitNew(_1738_exprGen);
              }
            }
            RAST._IExpr _1745_lhsGen;
            bool _1746_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1747_recIdents;
            DCOMP._IEnvironment _1748_resEnv;
            RAST._IExpr _out142;
            bool _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            DCOMP._IEnvironment _out145;
            (this).GenAssignLhs(_1736_lhs, _1738_exprGen, selfIdent, env, out _out142, out _out143, out _out144, out _out145);
            _1745_lhsGen = _out142;
            _1746_needsIIFE = _out143;
            _1747_recIdents = _out144;
            _1748_resEnv = _out145;
            generated = _1745_lhsGen;
            newEnv = _1748_resEnv;
            if (_1746_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1747_recIdents, _1740_exprIdents);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_If) {
          DAST._IExpression _1749_cond = _source87.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1750_thnDafny = _source87.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1751_elsDafny = _source87.dtor_els;
          unmatched87 = false;
          {
            RAST._IExpr _1752_cond;
            DCOMP._IOwnership _1753___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1754_recIdents;
            RAST._IExpr _out146;
            DCOMP._IOwnership _out147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
            (this).GenExpr(_1749_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out146, out _out147, out _out148);
            _1752_cond = _out146;
            _1753___v84 = _out147;
            _1754_recIdents = _out148;
            Dafny.ISequence<Dafny.Rune> _1755_condString;
            _1755_condString = (_1752_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1754_recIdents;
            RAST._IExpr _1756_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1757_thnIdents;
            DCOMP._IEnvironment _1758_thnEnv;
            RAST._IExpr _out149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out150;
            DCOMP._IEnvironment _out151;
            (this).GenStmts(_1750_thnDafny, selfIdent, env, isLast, earlyReturn, out _out149, out _out150, out _out151);
            _1756_thn = _out149;
            _1757_thnIdents = _out150;
            _1758_thnEnv = _out151;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1757_thnIdents);
            RAST._IExpr _1759_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1760_elsIdents;
            DCOMP._IEnvironment _1761_elsEnv;
            RAST._IExpr _out152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
            DCOMP._IEnvironment _out154;
            (this).GenStmts(_1751_elsDafny, selfIdent, env, isLast, earlyReturn, out _out152, out _out153, out _out154);
            _1759_els = _out152;
            _1760_elsIdents = _out153;
            _1761_elsEnv = _out154;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1760_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1752_cond, _1756_thn, _1759_els);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1762_lbl = _source87.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1763_body = _source87.dtor_body;
          unmatched87 = false;
          {
            RAST._IExpr _1764_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1765_bodyIdents;
            DCOMP._IEnvironment _1766_env2;
            RAST._IExpr _out155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
            DCOMP._IEnvironment _out157;
            (this).GenStmts(_1763_body, selfIdent, env, isLast, earlyReturn, out _out155, out _out156, out _out157);
            _1764_body = _out155;
            _1765_bodyIdents = _out156;
            _1766_env2 = _out157;
            readIdents = _1765_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1762_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1764_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_While) {
          DAST._IExpression _1767_cond = _source87.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1768_body = _source87.dtor_body;
          unmatched87 = false;
          {
            RAST._IExpr _1769_cond;
            DCOMP._IOwnership _1770___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1771_recIdents;
            RAST._IExpr _out158;
            DCOMP._IOwnership _out159;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
            (this).GenExpr(_1767_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out158, out _out159, out _out160);
            _1769_cond = _out158;
            _1770___v85 = _out159;
            _1771_recIdents = _out160;
            readIdents = _1771_recIdents;
            RAST._IExpr _1772_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1773_bodyIdents;
            DCOMP._IEnvironment _1774_bodyEnv;
            RAST._IExpr _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            DCOMP._IEnvironment _out163;
            (this).GenStmts(_1768_body, selfIdent, env, false, earlyReturn, out _out161, out _out162, out _out163);
            _1772_bodyExpr = _out161;
            _1773_bodyIdents = _out162;
            _1774_bodyEnv = _out163;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1773_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1769_cond), _1772_bodyExpr);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1775_boundName = _source87.dtor_boundName;
          DAST._IType _1776_boundType = _source87.dtor_boundType;
          DAST._IExpression _1777_overExpr = _source87.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1778_body = _source87.dtor_body;
          unmatched87 = false;
          {
            RAST._IExpr _1779_over;
            DCOMP._IOwnership _1780___v86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1781_recIdents;
            RAST._IExpr _out164;
            DCOMP._IOwnership _out165;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out166;
            (this).GenExpr(_1777_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out164, out _out165, out _out166);
            _1779_over = _out164;
            _1780___v86 = _out165;
            _1781_recIdents = _out166;
            if (((_1777_overExpr).is_MapBoundedPool) || ((_1777_overExpr).is_SetBoundedPool)) {
              _1779_over = ((_1779_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1782_boundTpe;
            RAST._IType _out167;
            _out167 = (this).GenType(_1776_boundType, DCOMP.GenTypeContext.@default());
            _1782_boundTpe = _out167;
            readIdents = _1781_recIdents;
            Dafny.ISequence<Dafny.Rune> _1783_boundRName;
            _1783_boundRName = DCOMP.__default.escapeVar(_1775_boundName);
            RAST._IExpr _1784_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1785_bodyIdents;
            DCOMP._IEnvironment _1786_bodyEnv;
            RAST._IExpr _out168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
            DCOMP._IEnvironment _out170;
            (this).GenStmts(_1778_body, selfIdent, (env).AddAssigned(_1783_boundRName, _1782_boundTpe), false, earlyReturn, out _out168, out _out169, out _out170);
            _1784_bodyExpr = _out168;
            _1785_bodyIdents = _out169;
            _1786_bodyEnv = _out170;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1785_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1783_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1783_boundRName, _1779_over, _1784_bodyExpr);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1787_toLabel = _source87.dtor_toLabel;
          unmatched87 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source88 = _1787_toLabel;
            bool unmatched88 = true;
            if (unmatched88) {
              if (_source88.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1788_lbl = _source88.dtor_value;
                unmatched88 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1788_lbl)));
                }
              }
            }
            if (unmatched88) {
              unmatched88 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1789_body = _source87.dtor_body;
          unmatched87 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1790_selfClone;
              DCOMP._IOwnership _1791___v87;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1792___v88;
              RAST._IExpr _out171;
              DCOMP._IOwnership _out172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out171, out _out172, out _out173);
              _1790_selfClone = _out171;
              _1791___v87 = _out172;
              _1792___v88 = _out173;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1790_selfClone)));
            }
            newEnv = env;
            BigInteger _hi35 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1793_paramI = BigInteger.Zero; _1793_paramI < _hi35; _1793_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1794_param;
              _1794_param = ((env).dtor_names).Select(_1793_paramI);
              RAST._IExpr _1795_paramInit;
              DCOMP._IOwnership _1796___v89;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1797___v90;
              RAST._IExpr _out174;
              DCOMP._IOwnership _out175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out176;
              (this).GenIdent(_1794_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out174, out _out175, out _out176);
              _1795_paramInit = _out174;
              _1796___v89 = _out175;
              _1797___v90 = _out176;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1794_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1795_paramInit)));
              if (((env).dtor_types).Contains(_1794_param)) {
                RAST._IType _1798_declaredType;
                _1798_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1794_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1794_param, _1798_declaredType);
              }
            }
            RAST._IExpr _1799_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1800_bodyIdents;
            DCOMP._IEnvironment _1801_bodyEnv;
            RAST._IExpr _out177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out178;
            DCOMP._IEnvironment _out179;
            (this).GenStmts(_1789_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out177, out _out178, out _out179);
            _1799_bodyExpr = _out177;
            _1800_bodyIdents = _out178;
            _1801_bodyEnv = _out179;
            readIdents = _1800_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1799_bodyExpr)));
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_JumpTailCallStart) {
          unmatched87 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Call) {
          DAST._IExpression _1802_on = _source87.dtor_on;
          DAST._ICallName _1803_name = _source87.dtor_callName;
          Dafny.ISequence<DAST._IType> _1804_typeArgs = _source87.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1805_args = _source87.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1806_maybeOutVars = _source87.dtor_outs;
          unmatched87 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1807_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1808_recIdents;
            Dafny.ISequence<RAST._IType> _1809_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1810_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out181;
            Dafny.ISequence<RAST._IType> _out182;
            Std.Wrappers._IOption<DAST._IResolvedType> _out183;
            (this).GenArgs(selfIdent, _1803_name, _1804_typeArgs, _1805_args, env, out _out180, out _out181, out _out182, out _out183);
            _1807_argExprs = _out180;
            _1808_recIdents = _out181;
            _1809_typeExprs = _out182;
            _1810_fullNameQualifier = _out183;
            readIdents = _1808_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source89 = _1810_fullNameQualifier;
            bool unmatched89 = true;
            if (unmatched89) {
              if (_source89.is_Some) {
                DAST._IResolvedType value9 = _source89.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1811_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1812_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1813_base = value9.dtor_kind;
                unmatched89 = false;
                RAST._IExpr _1814_fullPath;
                RAST._IExpr _out184;
                _out184 = DCOMP.COMP.GenPathExpr(_1811_path, true);
                _1814_fullPath = _out184;
                Dafny.ISequence<RAST._IType> _1815_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out185;
                _out185 = (this).GenTypeArgs(_1812_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1815_onTypeExprs = _out185;
                RAST._IExpr _1816_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1817_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1818_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1813_base).is_Trait) || ((_1813_base).is_Class)) {
                  RAST._IExpr _out186;
                  DCOMP._IOwnership _out187;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out188;
                  (this).GenExpr(_1802_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out186, out _out187, out _out188);
                  _1816_onExpr = _out186;
                  _1817_recOwnership = _out187;
                  _1818_recIdents = _out188;
                  _1816_onExpr = ((this).modify__macro).Apply1(_1816_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1818_recIdents);
                } else {
                  RAST._IExpr _out189;
                  DCOMP._IOwnership _out190;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out191;
                  (this).GenExpr(_1802_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out189, out _out190, out _out191);
                  _1816_onExpr = _out189;
                  _1817_recOwnership = _out190;
                  _1818_recIdents = _out191;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1818_recIdents);
                }
                generated = ((((_1814_fullPath).ApplyType(_1815_onTypeExprs)).FSel(DCOMP.__default.escapeName((_1803_name).dtor_name))).ApplyType(_1809_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1816_onExpr), _1807_argExprs));
              }
            }
            if (unmatched89) {
              unmatched89 = false;
              RAST._IExpr _1819_onExpr;
              DCOMP._IOwnership _1820___v95;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1821_enclosingIdents;
              RAST._IExpr _out192;
              DCOMP._IOwnership _out193;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
              (this).GenExpr(_1802_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out192, out _out193, out _out194);
              _1819_onExpr = _out192;
              _1820___v95 = _out193;
              _1821_enclosingIdents = _out194;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1821_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1822_renderedName;
              _1822_renderedName = (this).GetMethodName(_1802_on, _1803_name);
              DAST._IExpression _source90 = _1802_on;
              bool unmatched90 = true;
              if (unmatched90) {
                bool disjunctiveMatch13 = false;
                if (_source90.is_Companion) {
                  disjunctiveMatch13 = true;
                }
                if (_source90.is_ExternCompanion) {
                  disjunctiveMatch13 = true;
                }
                if (disjunctiveMatch13) {
                  unmatched90 = false;
                  {
                    _1819_onExpr = (_1819_onExpr).FSel(_1822_renderedName);
                  }
                }
              }
              if (unmatched90) {
                unmatched90 = false;
                {
                  if (!object.Equals(_1819_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source91 = _1803_name;
                    bool unmatched91 = true;
                    if (unmatched91) {
                      if (_source91.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source91.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1823_tpe = onType0.dtor_value;
                          unmatched91 = false;
                          RAST._IType _1824_typ;
                          RAST._IType _out195;
                          _out195 = (this).GenType(_1823_tpe, DCOMP.GenTypeContext.@default());
                          _1824_typ = _out195;
                          if (((_1824_typ).IsObjectOrPointer()) && (!object.Equals(_1819_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1819_onExpr = ((this).modify__macro).Apply1(_1819_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched91) {
                      unmatched91 = false;
                    }
                  }
                  _1819_onExpr = (_1819_onExpr).Sel(_1822_renderedName);
                }
              }
              generated = ((_1819_onExpr).ApplyType(_1809_typeExprs)).Apply(_1807_argExprs);
            }
            if (((_1806_maybeOutVars).is_Some) && ((new BigInteger(((_1806_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1825_outVar;
              _1825_outVar = DCOMP.__default.escapeVar(((_1806_maybeOutVars).dtor_value).Select(BigInteger.Zero));
              if (!((env).CanReadWithoutClone(_1825_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1825_outVar, generated);
            } else if (((_1806_maybeOutVars).is_None) || ((new BigInteger(((_1806_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1826_tmpVar;
              _1826_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1827_tmpId;
              _1827_tmpId = RAST.Expr.create_Identifier(_1826_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1826_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1828_outVars;
              _1828_outVars = (_1806_maybeOutVars).dtor_value;
              BigInteger _hi36 = new BigInteger((_1828_outVars).Count);
              for (BigInteger _1829_outI = BigInteger.Zero; _1829_outI < _hi36; _1829_outI++) {
                Dafny.ISequence<Dafny.Rune> _1830_outVar;
                _1830_outVar = DCOMP.__default.escapeVar((_1828_outVars).Select(_1829_outI));
                RAST._IExpr _1831_rhs;
                _1831_rhs = (_1827_tmpId).Sel(Std.Strings.__default.OfNat(_1829_outI));
                if (!((env).CanReadWithoutClone(_1830_outVar))) {
                  _1831_rhs = RAST.__default.MaybePlacebo(_1831_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1830_outVar, _1831_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Return) {
          DAST._IExpression _1832_exprDafny = _source87.dtor_expr;
          unmatched87 = false;
          {
            RAST._IExpr _1833_expr;
            DCOMP._IOwnership _1834___v105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1835_recIdents;
            RAST._IExpr _out196;
            DCOMP._IOwnership _out197;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out198;
            (this).GenExpr(_1832_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out196, out _out197, out _out198);
            _1833_expr = _out196;
            _1834___v105 = _out197;
            _1835_recIdents = _out198;
            readIdents = _1835_recIdents;
            if (isLast) {
              generated = _1833_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1833_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_EarlyReturn) {
          unmatched87 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source92 = earlyReturn;
            bool unmatched92 = true;
            if (unmatched92) {
              if (_source92.is_None) {
                unmatched92 = false;
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
              }
            }
            if (unmatched92) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1836_rustIdents = _source92.dtor_value;
              unmatched92 = false;
              Dafny.ISequence<RAST._IExpr> _1837_tupleArgs;
              _1837_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi37 = new BigInteger((_1836_rustIdents).Count);
              for (BigInteger _1838_i = BigInteger.Zero; _1838_i < _hi37; _1838_i++) {
                RAST._IExpr _1839_rIdent;
                DCOMP._IOwnership _1840___v106;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1841___v107;
                RAST._IExpr _out199;
                DCOMP._IOwnership _out200;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
                (this).GenIdent((_1836_rustIdents).Select(_1838_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out199, out _out200, out _out201);
                _1839_rIdent = _out199;
                _1840___v106 = _out200;
                _1841___v107 = _out201;
                _1837_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1837_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1839_rIdent));
              }
              if ((new BigInteger((_1837_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1837_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1837_tupleArgs)));
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Halt) {
          unmatched87 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched87) {
        DAST._IExpression _1842_e = _source87.dtor_Print_a0;
        unmatched87 = false;
        {
          RAST._IExpr _1843_printedExpr;
          DCOMP._IOwnership _1844_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1845_recIdents;
          RAST._IExpr _out202;
          DCOMP._IOwnership _out203;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out204;
          (this).GenExpr(_1842_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out202, out _out203, out _out204);
          _1843_printedExpr = _out202;
          _1844_recOwnership = _out203;
          _1845_recIdents = _out204;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).AsExpr()).Apply1(_1843_printedExpr)));
          readIdents = _1845_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeRangeToRustType(DAST._INewtypeRange range) {
      DAST._INewtypeRange _source93 = range;
      bool unmatched93 = true;
      if (unmatched93) {
        if (_source93.is_NoRange) {
          unmatched93 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched93) {
        if (_source93.is_U8) {
          unmatched93 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched93) {
        if (_source93.is_U16) {
          unmatched93 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched93) {
        if (_source93.is_U32) {
          unmatched93 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched93) {
        if (_source93.is_U64) {
          unmatched93 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched93) {
        if (_source93.is_U128) {
          unmatched93 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched93) {
        if (_source93.is_I8) {
          unmatched93 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched93) {
        if (_source93.is_I16) {
          unmatched93 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched93) {
        if (_source93.is_I32) {
          unmatched93 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched93) {
        if (_source93.is_I64) {
          unmatched93 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched93) {
        if (_source93.is_I128) {
          unmatched93 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched93) {
        unmatched93 = false;
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
        RAST._IExpr _out205;
        DCOMP._IOwnership _out206;
        (this).FromOwned(r, expectedOwnership, out _out205, out _out206);
        @out = _out205;
        resultingOwnership = _out206;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out207;
        DCOMP._IOwnership _out208;
        (this).FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out207, out _out208);
        @out = _out207;
        resultingOwnership = _out208;
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
      DAST._IExpression _source94 = e;
      bool unmatched94 = true;
      if (unmatched94) {
        if (_source94.is_Literal) {
          DAST._ILiteral _h170 = _source94.dtor_Literal_a0;
          if (_h170.is_BoolLiteral) {
            bool _1846_b = _h170.dtor_BoolLiteral_a0;
            unmatched94 = false;
            {
              RAST._IExpr _out209;
              DCOMP._IOwnership _out210;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1846_b), expectedOwnership, out _out209, out _out210);
              r = _out209;
              resultingOwnership = _out210;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched94) {
        if (_source94.is_Literal) {
          DAST._ILiteral _h171 = _source94.dtor_Literal_a0;
          if (_h171.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1847_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1848_t = _h171.dtor_IntLiteral_a1;
            unmatched94 = false;
            {
              DAST._IType _source95 = _1848_t;
              bool unmatched95 = true;
              if (unmatched95) {
                if (_source95.is_Primitive) {
                  DAST._IPrimitive _h70 = _source95.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched95 = false;
                    {
                      if ((new BigInteger((_1847_i).Count)) <= (new BigInteger(4))) {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralInt(_1847_i));
                      } else {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1847_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched95) {
                DAST._IType _1849_o = _source95;
                unmatched95 = false;
                {
                  RAST._IType _1850_genType;
                  RAST._IType _out211;
                  _out211 = (this).GenType(_1849_o, DCOMP.GenTypeContext.@default());
                  _1850_genType = _out211;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1847_i), _1850_genType);
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
      if (unmatched94) {
        if (_source94.is_Literal) {
          DAST._ILiteral _h172 = _source94.dtor_Literal_a0;
          if (_h172.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1851_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1852_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1853_t = _h172.dtor_DecLiteral_a2;
            unmatched94 = false;
            {
              DAST._IType _source96 = _1853_t;
              bool unmatched96 = true;
              if (unmatched96) {
                if (_source96.is_Primitive) {
                  DAST._IPrimitive _h71 = _source96.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched96 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1851_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1852_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched96) {
                DAST._IType _1854_o = _source96;
                unmatched96 = false;
                {
                  RAST._IType _1855_genType;
                  RAST._IType _out214;
                  _out214 = (this).GenType(_1854_o, DCOMP.GenTypeContext.@default());
                  _1855_genType = _out214;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1851_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1852_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1855_genType);
                }
              }
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
      if (unmatched94) {
        if (_source94.is_Literal) {
          DAST._ILiteral _h173 = _source94.dtor_Literal_a0;
          if (_h173.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1856_l = _h173.dtor_StringLiteral_a0;
            bool _1857_verbatim = _h173.dtor_verbatim;
            unmatched94 = false;
            {
              if (_1857_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = (((RAST.__default.dafny__runtime).MSel((this).string__of)).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1856_l, false, _1857_verbatim));
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
      if (unmatched94) {
        if (_source94.is_Literal) {
          DAST._ILiteral _h174 = _source94.dtor_Literal_a0;
          if (_h174.is_CharLiteralUTF16) {
            BigInteger _1858_c = _h174.dtor_CharLiteralUTF16_a0;
            unmatched94 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1858_c));
              r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              r = (((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(r);
              RAST._IExpr _out219;
              DCOMP._IOwnership _out220;
              (this).FromOwned(r, expectedOwnership, out _out219, out _out220);
              r = _out219;
              resultingOwnership = _out220;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched94) {
        if (_source94.is_Literal) {
          DAST._ILiteral _h175 = _source94.dtor_Literal_a0;
          if (_h175.is_CharLiteral) {
            Dafny.Rune _1859_c = _h175.dtor_CharLiteral_a0;
            unmatched94 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1859_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(r);
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
      }
      if (unmatched94) {
        DAST._ILiteral _h176 = _source94.dtor_Literal_a0;
        DAST._IType _1860_tpe = _h176.dtor_Null_a0;
        unmatched94 = false;
        {
          RAST._IType _1861_tpeGen;
          RAST._IType _out223;
          _out223 = (this).GenType(_1860_tpe, DCOMP.GenTypeContext.@default());
          _1861_tpeGen = _out223;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null_mut"));
          } else {
            r = RAST.Expr.create_TypeAscription((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1861_tpeGen);
          }
          RAST._IExpr _out224;
          DCOMP._IOwnership _out225;
          (this).FromOwned(r, expectedOwnership, out _out224, out _out225);
          r = _out224;
          resultingOwnership = _out225;
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
      DAST._IExpression _let_tmp_rhs56 = e;
      DAST._IBinOp _1862_op = _let_tmp_rhs56.dtor_op;
      DAST._IExpression _1863_lExpr = _let_tmp_rhs56.dtor_left;
      DAST._IExpression _1864_rExpr = _let_tmp_rhs56.dtor_right;
      DAST.Format._IBinaryOpFormat _1865_format = _let_tmp_rhs56.dtor_format2;
      bool _1866_becomesLeftCallsRight;
      _1866_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source97 = _1862_op;
        bool unmatched97 = true;
        if (unmatched97) {
          bool disjunctiveMatch14 = false;
          if (_source97.is_SetMerge) {
            disjunctiveMatch14 = true;
          }
          if (_source97.is_SetSubtraction) {
            disjunctiveMatch14 = true;
          }
          if (_source97.is_SetIntersection) {
            disjunctiveMatch14 = true;
          }
          if (_source97.is_SetDisjoint) {
            disjunctiveMatch14 = true;
          }
          if (_source97.is_MapMerge) {
            disjunctiveMatch14 = true;
          }
          if (_source97.is_MapSubtraction) {
            disjunctiveMatch14 = true;
          }
          if (_source97.is_MultisetMerge) {
            disjunctiveMatch14 = true;
          }
          if (_source97.is_MultisetSubtraction) {
            disjunctiveMatch14 = true;
          }
          if (_source97.is_MultisetIntersection) {
            disjunctiveMatch14 = true;
          }
          if (_source97.is_MultisetDisjoint) {
            disjunctiveMatch14 = true;
          }
          if (_source97.is_Concat) {
            disjunctiveMatch14 = true;
          }
          if (disjunctiveMatch14) {
            unmatched97 = false;
            return true;
          }
        }
        if (unmatched97) {
          unmatched97 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1867_becomesRightCallsLeft;
      _1867_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source98 = _1862_op;
        bool unmatched98 = true;
        if (unmatched98) {
          if (_source98.is_In) {
            unmatched98 = false;
            return true;
          }
        }
        if (unmatched98) {
          unmatched98 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1868_becomesCallLeftRight;
      _1868_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source99 = _1862_op;
        bool unmatched99 = true;
        if (unmatched99) {
          if (_source99.is_Eq) {
            bool referential0 = _source99.dtor_referential;
            if ((referential0) == (true)) {
              unmatched99 = false;
              return false;
            }
          }
        }
        if (unmatched99) {
          if (_source99.is_SetMerge) {
            unmatched99 = false;
            return true;
          }
        }
        if (unmatched99) {
          if (_source99.is_SetSubtraction) {
            unmatched99 = false;
            return true;
          }
        }
        if (unmatched99) {
          if (_source99.is_SetIntersection) {
            unmatched99 = false;
            return true;
          }
        }
        if (unmatched99) {
          if (_source99.is_SetDisjoint) {
            unmatched99 = false;
            return true;
          }
        }
        if (unmatched99) {
          if (_source99.is_MapMerge) {
            unmatched99 = false;
            return true;
          }
        }
        if (unmatched99) {
          if (_source99.is_MapSubtraction) {
            unmatched99 = false;
            return true;
          }
        }
        if (unmatched99) {
          if (_source99.is_MultisetMerge) {
            unmatched99 = false;
            return true;
          }
        }
        if (unmatched99) {
          if (_source99.is_MultisetSubtraction) {
            unmatched99 = false;
            return true;
          }
        }
        if (unmatched99) {
          if (_source99.is_MultisetIntersection) {
            unmatched99 = false;
            return true;
          }
        }
        if (unmatched99) {
          if (_source99.is_MultisetDisjoint) {
            unmatched99 = false;
            return true;
          }
        }
        if (unmatched99) {
          if (_source99.is_Concat) {
            unmatched99 = false;
            return true;
          }
        }
        if (unmatched99) {
          unmatched99 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1869_expectedLeftOwnership;
      _1869_expectedLeftOwnership = ((_1866_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1867_becomesRightCallsLeft) || (_1868_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1870_expectedRightOwnership;
      _1870_expectedRightOwnership = (((_1866_becomesLeftCallsRight) || (_1868_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1867_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1871_left;
      DCOMP._IOwnership _1872___v112;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1873_recIdentsL;
      RAST._IExpr _out226;
      DCOMP._IOwnership _out227;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
      (this).GenExpr(_1863_lExpr, selfIdent, env, _1869_expectedLeftOwnership, out _out226, out _out227, out _out228);
      _1871_left = _out226;
      _1872___v112 = _out227;
      _1873_recIdentsL = _out228;
      RAST._IExpr _1874_right;
      DCOMP._IOwnership _1875___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1876_recIdentsR;
      RAST._IExpr _out229;
      DCOMP._IOwnership _out230;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out231;
      (this).GenExpr(_1864_rExpr, selfIdent, env, _1870_expectedRightOwnership, out _out229, out _out230, out _out231);
      _1874_right = _out229;
      _1875___v113 = _out230;
      _1876_recIdentsR = _out231;
      DAST._IBinOp _source100 = _1862_op;
      bool unmatched100 = true;
      if (unmatched100) {
        if (_source100.is_In) {
          unmatched100 = false;
          {
            r = ((_1874_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1871_left);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_SeqProperPrefix) {
          unmatched100 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1871_left, _1874_right, _1865_format);
        }
      }
      if (unmatched100) {
        if (_source100.is_SeqPrefix) {
          unmatched100 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1871_left, _1874_right, _1865_format);
        }
      }
      if (unmatched100) {
        if (_source100.is_SetMerge) {
          unmatched100 = false;
          {
            r = ((_1871_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1874_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_SetSubtraction) {
          unmatched100 = false;
          {
            r = ((_1871_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1874_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_SetIntersection) {
          unmatched100 = false;
          {
            r = ((_1871_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1874_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_Subset) {
          unmatched100 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1871_left, _1874_right, _1865_format);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_ProperSubset) {
          unmatched100 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1871_left, _1874_right, _1865_format);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_SetDisjoint) {
          unmatched100 = false;
          {
            r = ((_1871_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1874_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MapMerge) {
          unmatched100 = false;
          {
            r = ((_1871_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1874_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MapSubtraction) {
          unmatched100 = false;
          {
            r = ((_1871_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1874_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MultisetMerge) {
          unmatched100 = false;
          {
            r = ((_1871_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1874_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MultisetSubtraction) {
          unmatched100 = false;
          {
            r = ((_1871_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1874_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MultisetIntersection) {
          unmatched100 = false;
          {
            r = ((_1871_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1874_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_Submultiset) {
          unmatched100 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1871_left, _1874_right, _1865_format);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_ProperSubmultiset) {
          unmatched100 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1871_left, _1874_right, _1865_format);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MultisetDisjoint) {
          unmatched100 = false;
          {
            r = ((_1871_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1874_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_Concat) {
          unmatched100 = false;
          {
            r = ((_1871_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1874_right);
          }
        }
      }
      if (unmatched100) {
        unmatched100 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1862_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1862_op), _1871_left, _1874_right, _1865_format);
          } else {
            DAST._IBinOp _source101 = _1862_op;
            bool unmatched101 = true;
            if (unmatched101) {
              if (_source101.is_Eq) {
                bool _1877_referential = _source101.dtor_referential;
                unmatched101 = false;
                {
                  if (_1877_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1871_left, _1874_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1864_rExpr).is_SeqValue) && ((new BigInteger(((_1864_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1871_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1863_lExpr).is_SeqValue) && ((new BigInteger(((_1863_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1874_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1871_left, _1874_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched101) {
              if (_source101.is_EuclidianDiv) {
                unmatched101 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1871_left, _1874_right));
                }
              }
            }
            if (unmatched101) {
              if (_source101.is_EuclidianMod) {
                unmatched101 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1871_left, _1874_right));
                }
              }
            }
            if (unmatched101) {
              Dafny.ISequence<Dafny.Rune> _1878_op = _source101.dtor_Passthrough_a0;
              unmatched101 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1878_op, _1871_left, _1874_right, _1865_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out232;
      DCOMP._IOwnership _out233;
      (this).FromOwned(r, expectedOwnership, out _out232, out _out233);
      r = _out232;
      resultingOwnership = _out233;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1873_recIdentsL, _1876_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs57 = e;
      DAST._IExpression _1879_expr = _let_tmp_rhs57.dtor_value;
      DAST._IType _1880_fromTpe = _let_tmp_rhs57.dtor_from;
      DAST._IType _1881_toTpe = _let_tmp_rhs57.dtor_typ;
      DAST._IType _let_tmp_rhs58 = _1881_toTpe;
      DAST._IResolvedType _let_tmp_rhs59 = _let_tmp_rhs58.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1882_path = _let_tmp_rhs59.dtor_path;
      Dafny.ISequence<DAST._IType> _1883_typeArgs = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs60 = _let_tmp_rhs59.dtor_kind;
      DAST._IType _1884_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _1885_range = _let_tmp_rhs60.dtor_range;
      bool _1886_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1887___v115 = _let_tmp_rhs59.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1888___v116 = _let_tmp_rhs59.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1889___v117 = _let_tmp_rhs59.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1890_nativeToType;
      _1890_nativeToType = DCOMP.COMP.NewtypeRangeToRustType(_1885_range);
      if (object.Equals(_1880_fromTpe, _1884_b)) {
        RAST._IExpr _1891_recursiveGen;
        DCOMP._IOwnership _1892_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1893_recIdents;
        RAST._IExpr _out234;
        DCOMP._IOwnership _out235;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out236;
        (this).GenExpr(_1879_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out234, out _out235, out _out236);
        _1891_recursiveGen = _out234;
        _1892_recOwned = _out235;
        _1893_recIdents = _out236;
        readIdents = _1893_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source102 = _1890_nativeToType;
        bool unmatched102 = true;
        if (unmatched102) {
          if (_source102.is_Some) {
            RAST._IType _1894_v = _source102.dtor_value;
            unmatched102 = false;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1891_recursiveGen, RAST.Expr.create_ExprFromType(_1894_v)));
            RAST._IExpr _out237;
            DCOMP._IOwnership _out238;
            (this).FromOwned(r, expectedOwnership, out _out237, out _out238);
            r = _out237;
            resultingOwnership = _out238;
          }
        }
        if (unmatched102) {
          unmatched102 = false;
          if (_1886_erase) {
            r = _1891_recursiveGen;
          } else {
            RAST._IType _1895_rhsType;
            RAST._IType _out239;
            _out239 = (this).GenType(_1881_toTpe, DCOMP.GenTypeContext.InBinding());
            _1895_rhsType = _out239;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1895_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1891_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out240;
          DCOMP._IOwnership _out241;
          (this).FromOwnership(r, _1892_recOwned, expectedOwnership, out _out240, out _out241);
          r = _out240;
          resultingOwnership = _out241;
        }
      } else {
        if ((_1890_nativeToType).is_Some) {
          DAST._IType _source103 = _1880_fromTpe;
          bool unmatched103 = true;
          if (unmatched103) {
            if (_source103.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source103.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1896_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1897_range0 = kind1.dtor_range;
                bool _1898_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1899_attributes0 = resolved1.dtor_attributes;
                unmatched103 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1900_nativeFromType;
                  _1900_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1897_range0);
                  if ((_1900_nativeFromType).is_Some) {
                    RAST._IExpr _1901_recursiveGen;
                    DCOMP._IOwnership _1902_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1903_recIdents;
                    RAST._IExpr _out242;
                    DCOMP._IOwnership _out243;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out244;
                    (this).GenExpr(_1879_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out242, out _out243, out _out244);
                    _1901_recursiveGen = _out242;
                    _1902_recOwned = _out243;
                    _1903_recIdents = _out244;
                    RAST._IExpr _out245;
                    DCOMP._IOwnership _out246;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1901_recursiveGen, (_1890_nativeToType).dtor_value), _1902_recOwned, expectedOwnership, out _out245, out _out246);
                    r = _out245;
                    resultingOwnership = _out246;
                    readIdents = _1903_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched103) {
            unmatched103 = false;
          }
          if (object.Equals(_1880_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1904_recursiveGen;
            DCOMP._IOwnership _1905_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1906_recIdents;
            RAST._IExpr _out247;
            DCOMP._IOwnership _out248;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
            (this).GenExpr(_1879_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out247, out _out248, out _out249);
            _1904_recursiveGen = _out247;
            _1905_recOwned = _out248;
            _1906_recIdents = _out249;
            RAST._IExpr _out250;
            DCOMP._IOwnership _out251;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1904_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1890_nativeToType).dtor_value), _1905_recOwned, expectedOwnership, out _out250, out _out251);
            r = _out250;
            resultingOwnership = _out251;
            readIdents = _1906_recIdents;
            return ;
          }
        }
        RAST._IExpr _out252;
        DCOMP._IOwnership _out253;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out254;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1879_expr, _1880_fromTpe, _1884_b), _1884_b, _1881_toTpe), selfIdent, env, expectedOwnership, out _out252, out _out253, out _out254);
        r = _out252;
        resultingOwnership = _out253;
        readIdents = _out254;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs61 = e;
      DAST._IExpression _1907_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _1908_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _1909_toTpe = _let_tmp_rhs61.dtor_typ;
      DAST._IType _let_tmp_rhs62 = _1908_fromTpe;
      DAST._IResolvedType _let_tmp_rhs63 = _let_tmp_rhs62.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1910___v123 = _let_tmp_rhs63.dtor_path;
      Dafny.ISequence<DAST._IType> _1911___v124 = _let_tmp_rhs63.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs64 = _let_tmp_rhs63.dtor_kind;
      DAST._IType _1912_b = _let_tmp_rhs64.dtor_baseType;
      DAST._INewtypeRange _1913_range = _let_tmp_rhs64.dtor_range;
      bool _1914_erase = _let_tmp_rhs64.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1915_attributes = _let_tmp_rhs63.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1916___v125 = _let_tmp_rhs63.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1917___v126 = _let_tmp_rhs63.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1918_nativeFromType;
      _1918_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1913_range);
      if (object.Equals(_1912_b, _1909_toTpe)) {
        RAST._IExpr _1919_recursiveGen;
        DCOMP._IOwnership _1920_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1921_recIdents;
        RAST._IExpr _out255;
        DCOMP._IOwnership _out256;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out257;
        (this).GenExpr(_1907_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out255, out _out256, out _out257);
        _1919_recursiveGen = _out255;
        _1920_recOwned = _out256;
        _1921_recIdents = _out257;
        readIdents = _1921_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source104 = _1918_nativeFromType;
        bool unmatched104 = true;
        if (unmatched104) {
          if (_source104.is_Some) {
            RAST._IType _1922_v = _source104.dtor_value;
            unmatched104 = false;
            RAST._IType _1923_toTpeRust;
            RAST._IType _out258;
            _out258 = (this).GenType(_1909_toTpe, DCOMP.GenTypeContext.@default());
            _1923_toTpeRust = _out258;
            r = ((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1923_toTpeRust))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1919_recursiveGen));
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            (this).FromOwned(r, expectedOwnership, out _out259, out _out260);
            r = _out259;
            resultingOwnership = _out260;
          }
        }
        if (unmatched104) {
          unmatched104 = false;
          if (_1914_erase) {
            r = _1919_recursiveGen;
          } else {
            r = (_1919_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out261;
          DCOMP._IOwnership _out262;
          (this).FromOwnership(r, _1920_recOwned, expectedOwnership, out _out261, out _out262);
          r = _out261;
          resultingOwnership = _out262;
        }
      } else {
        if ((_1918_nativeFromType).is_Some) {
          if (object.Equals(_1909_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1924_recursiveGen;
            DCOMP._IOwnership _1925_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1926_recIdents;
            RAST._IExpr _out263;
            DCOMP._IOwnership _out264;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out265;
            (this).GenExpr(_1907_expr, selfIdent, env, expectedOwnership, out _out263, out _out264, out _out265);
            _1924_recursiveGen = _out263;
            _1925_recOwned = _out264;
            _1926_recIdents = _out265;
            RAST._IExpr _out266;
            DCOMP._IOwnership _out267;
            (this).FromOwnership((((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(RAST.Expr.create_TypeAscription(_1924_recursiveGen, (this).DafnyCharUnderlying)), _1925_recOwned, expectedOwnership, out _out266, out _out267);
            r = _out266;
            resultingOwnership = _out267;
            readIdents = _1926_recIdents;
            return ;
          }
        }
        RAST._IExpr _out268;
        DCOMP._IOwnership _out269;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1907_expr, _1908_fromTpe, _1912_b), _1912_b, _1909_toTpe), selfIdent, env, expectedOwnership, out _out268, out _out269, out _out270);
        r = _out268;
        resultingOwnership = _out269;
        readIdents = _out270;
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
        Std.Wrappers._IResult<__T, __E> _1927_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1927_valueOrError0).IsFailure()) {
          return (_1927_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1928_head = (_1927_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1929_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1929_valueOrError1).IsFailure()) {
            return (_1929_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1930_tail = (_1929_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1928_head), _1930_tail));
          }
        }
      }
    }
    public Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> UpcastConversionLambda(DAST._IType fromType, RAST._IType fromTpe, DAST._IType toType, RAST._IType toTpe, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> typeParams)
    {
      if (object.Equals(fromTpe, toTpe)) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_id"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(fromTpe))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
      } else if (((fromTpe).IsObjectOrPointer()) && ((toTpe).IsObjectOrPointer())) {
        if (!(((toTpe).ObjectOrPointerUnderlying()).is_DynType)) {
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Failure(_System.Tuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>.create(fromType, fromTpe, toType, toTpe, typeParams));
        } else {
          RAST._IType _1931_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1932_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel((this).upcast)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1931_fromTpeUnderlying, _1932_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1933_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1933_valueOrError0).IsFailure()) {
          return (_1933_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1934_lambda = (_1933_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1934_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).AsExpr()).Apply1(_1934_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1935_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim14 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr14 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim14, "array size exceeds memory limit")];
          for (int i14 = 0; i14 < dim14; i14++) {
            var _1936_i = (BigInteger) i14;
            arr14[(int)(_1936_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_1936_i), ((fromTpe).dtor_arguments).Select(_1936_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_1936_i), ((toTpe).dtor_arguments).Select(_1936_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr14);
        }))());
        if ((_1935_valueOrError1).IsFailure()) {
          return (_1935_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1937_lambdas = (_1935_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim15 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr15 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim15, "array size exceeds memory limit")];
  for (int i15 = 0; i15 < dim15; i15++) {
    var _1938_i = (BigInteger) i15;
    arr15[(int)(_1938_i)] = ((fromTpe).dtor_arguments).Select(_1938_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr15);
}))())).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1937_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1939_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1940_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1941_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1942_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1943_valueOrError2 = (this).UpcastConversionLambda(_1941_newFromType, _1939_newFromTpe, _1942_newToType, _1940_newToTpe, typeParams);
        if ((_1943_valueOrError2).IsFailure()) {
          return (_1943_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1944_coerceArg = (_1943_valueOrError2).Extract();
          RAST._IPath _1945_collectionType = (RAST.__default.dafny__runtime).MSel(((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name);
          RAST._IExpr _1946_baseType = (((((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? (((_1945_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((((fromTpe).Expand()).dtor_arguments).Select(BigInteger.Zero), _1939_newFromTpe))) : (((_1945_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1939_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1946_baseType).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1944_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1947_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1947_valueOrError3).IsFailure()) {
          return (_1947_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1948_lambda = (_1947_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1948_lambda));
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
      DAST._IExpression _let_tmp_rhs65 = e;
      DAST._IExpression _1949_expr = _let_tmp_rhs65.dtor_value;
      DAST._IType _1950_fromTpe = _let_tmp_rhs65.dtor_from;
      DAST._IType _1951_toTpe = _let_tmp_rhs65.dtor_typ;
      RAST._IType _1952_fromTpeGen;
      RAST._IType _out271;
      _out271 = (this).GenType(_1950_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1952_fromTpeGen = _out271;
      RAST._IType _1953_toTpeGen;
      RAST._IType _out272;
      _out272 = (this).GenType(_1951_toTpe, DCOMP.GenTypeContext.InBinding());
      _1953_toTpeGen = _out272;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1954_upcastConverter;
      _1954_upcastConverter = (this).UpcastConversionLambda(_1950_fromTpe, _1952_fromTpeGen, _1951_toTpe, _1953_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1954_upcastConverter).is_Success) {
        RAST._IExpr _1955_conversionLambda;
        _1955_conversionLambda = (_1954_upcastConverter).dtor_value;
        RAST._IExpr _1956_recursiveGen;
        DCOMP._IOwnership _1957_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1958_recIdents;
        RAST._IExpr _out273;
        DCOMP._IOwnership _out274;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out275;
        (this).GenExpr(_1949_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out273, out _out274, out _out275);
        _1956_recursiveGen = _out273;
        _1957_recOwned = _out274;
        _1958_recIdents = _out275;
        readIdents = _1958_recIdents;
        r = (_1955_conversionLambda).Apply1(_1956_recursiveGen);
        RAST._IExpr _out276;
        DCOMP._IOwnership _out277;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out276, out _out277);
        r = _out276;
        resultingOwnership = _out277;
      } else if ((this).IsDowncastConversion(_1952_fromTpeGen, _1953_toTpeGen)) {
        RAST._IExpr _1959_recursiveGen;
        DCOMP._IOwnership _1960_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1961_recIdents;
        RAST._IExpr _out278;
        DCOMP._IOwnership _out279;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out280;
        (this).GenExpr(_1949_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out278, out _out279, out _out280);
        _1959_recursiveGen = _out278;
        _1960_recOwned = _out279;
        _1961_recIdents = _out280;
        readIdents = _1961_recIdents;
        _1953_toTpeGen = (_1953_toTpeGen).ObjectOrPointerUnderlying();
        r = (((RAST.__default.dafny__runtime).MSel((this).downcast)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1959_recursiveGen, RAST.Expr.create_ExprFromType(_1953_toTpeGen)));
        RAST._IExpr _out281;
        DCOMP._IOwnership _out282;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out281, out _out282);
        r = _out281;
        resultingOwnership = _out282;
      } else {
        RAST._IExpr _1962_recursiveGen;
        DCOMP._IOwnership _1963_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1964_recIdents;
        RAST._IExpr _out283;
        DCOMP._IOwnership _out284;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out285;
        (this).GenExpr(_1949_expr, selfIdent, env, expectedOwnership, out _out283, out _out284, out _out285);
        _1962_recursiveGen = _out283;
        _1963_recOwned = _out284;
        _1964_recIdents = _out285;
        readIdents = _1964_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs66 = _1954_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs67 = _let_tmp_rhs66.dtor_error;
        DAST._IType _1965_fromType = _let_tmp_rhs67.dtor__0;
        RAST._IType _1966_fromTpeGen = _let_tmp_rhs67.dtor__1;
        DAST._IType _1967_toType = _let_tmp_rhs67.dtor__2;
        RAST._IType _1968_toTpeGen = _let_tmp_rhs67.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1969_m = _let_tmp_rhs67.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1970_msg;
        _1970_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1966_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1968_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1970_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1962_recursiveGen)._ToString(DCOMP.__default.IND), _1970_msg));
        RAST._IExpr _out286;
        DCOMP._IOwnership _out287;
        (this).FromOwnership(r, _1963_recOwned, expectedOwnership, out _out286, out _out287);
        r = _out286;
        resultingOwnership = _out287;
      }
    }
    public void GenExprConvert(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs68 = e;
      DAST._IExpression _1971_expr = _let_tmp_rhs68.dtor_value;
      DAST._IType _1972_fromTpe = _let_tmp_rhs68.dtor_from;
      DAST._IType _1973_toTpe = _let_tmp_rhs68.dtor_typ;
      if (object.Equals(_1972_fromTpe, _1973_toTpe)) {
        RAST._IExpr _1974_recursiveGen;
        DCOMP._IOwnership _1975_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1976_recIdents;
        RAST._IExpr _out288;
        DCOMP._IOwnership _out289;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
        (this).GenExpr(_1971_expr, selfIdent, env, expectedOwnership, out _out288, out _out289, out _out290);
        _1974_recursiveGen = _out288;
        _1975_recOwned = _out289;
        _1976_recIdents = _out290;
        r = _1974_recursiveGen;
        RAST._IExpr _out291;
        DCOMP._IOwnership _out292;
        (this).FromOwnership(r, _1975_recOwned, expectedOwnership, out _out291, out _out292);
        r = _out291;
        resultingOwnership = _out292;
        readIdents = _1976_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source105 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1972_fromTpe, _1973_toTpe);
        bool unmatched105 = true;
        if (unmatched105) {
          DAST._IType _10 = _source105.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1977_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1978_range = kind2.dtor_range;
              bool _1979_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1980_attributes = resolved2.dtor_attributes;
              unmatched105 = false;
              {
                RAST._IExpr _out293;
                DCOMP._IOwnership _out294;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out295;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out293, out _out294, out _out295);
                r = _out293;
                resultingOwnership = _out294;
                readIdents = _out295;
              }
            }
          }
        }
        if (unmatched105) {
          DAST._IType _00 = _source105.dtor__0;
          if (_00.is_UserDefined) {
            DAST._IResolvedType resolved3 = _00.dtor_resolved;
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1981_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1982_range = kind3.dtor_range;
              bool _1983_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1984_attributes = resolved3.dtor_attributes;
              unmatched105 = false;
              {
                RAST._IExpr _out296;
                DCOMP._IOwnership _out297;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out296, out _out297, out _out298);
                r = _out296;
                resultingOwnership = _out297;
                readIdents = _out298;
              }
            }
          }
        }
        if (unmatched105) {
          DAST._IType _01 = _source105.dtor__0;
          if (_01.is_Primitive) {
            DAST._IPrimitive _h72 = _01.dtor_Primitive_a0;
            if (_h72.is_Int) {
              DAST._IType _11 = _source105.dtor__1;
              if (_11.is_Primitive) {
                DAST._IPrimitive _h73 = _11.dtor_Primitive_a0;
                if (_h73.is_Real) {
                  unmatched105 = false;
                  {
                    RAST._IExpr _1985_recursiveGen;
                    DCOMP._IOwnership _1986___v137;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1987_recIdents;
                    RAST._IExpr _out299;
                    DCOMP._IOwnership _out300;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out301;
                    (this).GenExpr(_1971_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out299, out _out300, out _out301);
                    _1985_recursiveGen = _out299;
                    _1986___v137 = _out300;
                    _1987_recIdents = _out301;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1985_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out302;
                    DCOMP._IOwnership _out303;
                    (this).FromOwned(r, expectedOwnership, out _out302, out _out303);
                    r = _out302;
                    resultingOwnership = _out303;
                    readIdents = _1987_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched105) {
          DAST._IType _02 = _source105.dtor__0;
          if (_02.is_Primitive) {
            DAST._IPrimitive _h74 = _02.dtor_Primitive_a0;
            if (_h74.is_Real) {
              DAST._IType _12 = _source105.dtor__1;
              if (_12.is_Primitive) {
                DAST._IPrimitive _h75 = _12.dtor_Primitive_a0;
                if (_h75.is_Int) {
                  unmatched105 = false;
                  {
                    RAST._IExpr _1988_recursiveGen;
                    DCOMP._IOwnership _1989___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1990_recIdents;
                    RAST._IExpr _out304;
                    DCOMP._IOwnership _out305;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out306;
                    (this).GenExpr(_1971_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out304, out _out305, out _out306);
                    _1988_recursiveGen = _out304;
                    _1989___v138 = _out305;
                    _1990_recIdents = _out306;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1988_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out307;
                    DCOMP._IOwnership _out308;
                    (this).FromOwned(r, expectedOwnership, out _out307, out _out308);
                    r = _out307;
                    resultingOwnership = _out308;
                    readIdents = _1990_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched105) {
          DAST._IType _03 = _source105.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h76 = _03.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _13 = _source105.dtor__1;
              if (_13.is_Passthrough) {
                unmatched105 = false;
                {
                  RAST._IType _1991_rhsType;
                  RAST._IType _out309;
                  _out309 = (this).GenType(_1973_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1991_rhsType = _out309;
                  RAST._IExpr _1992_recursiveGen;
                  DCOMP._IOwnership _1993___v140;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1994_recIdents;
                  RAST._IExpr _out310;
                  DCOMP._IOwnership _out311;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out312;
                  (this).GenExpr(_1971_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out310, out _out311, out _out312);
                  _1992_recursiveGen = _out310;
                  _1993___v140 = _out311;
                  _1994_recIdents = _out312;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1991_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1992_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out313;
                  DCOMP._IOwnership _out314;
                  (this).FromOwned(r, expectedOwnership, out _out313, out _out314);
                  r = _out313;
                  resultingOwnership = _out314;
                  readIdents = _1994_recIdents;
                }
              }
            }
          }
        }
        if (unmatched105) {
          DAST._IType _04 = _source105.dtor__0;
          if (_04.is_Passthrough) {
            DAST._IType _14 = _source105.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h77 = _14.dtor_Primitive_a0;
              if (_h77.is_Int) {
                unmatched105 = false;
                {
                  RAST._IType _1995_rhsType;
                  RAST._IType _out315;
                  _out315 = (this).GenType(_1972_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1995_rhsType = _out315;
                  RAST._IExpr _1996_recursiveGen;
                  DCOMP._IOwnership _1997___v142;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1998_recIdents;
                  RAST._IExpr _out316;
                  DCOMP._IOwnership _out317;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out318;
                  (this).GenExpr(_1971_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out316, out _out317, out _out318);
                  _1996_recursiveGen = _out316;
                  _1997___v142 = _out317;
                  _1998_recIdents = _out318;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1996_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out319;
                  DCOMP._IOwnership _out320;
                  (this).FromOwned(r, expectedOwnership, out _out319, out _out320);
                  r = _out319;
                  resultingOwnership = _out320;
                  readIdents = _1998_recIdents;
                }
              }
            }
          }
        }
        if (unmatched105) {
          DAST._IType _05 = _source105.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h78 = _05.dtor_Primitive_a0;
            if (_h78.is_Int) {
              DAST._IType _15 = _source105.dtor__1;
              if (_15.is_Primitive) {
                DAST._IPrimitive _h79 = _15.dtor_Primitive_a0;
                if (_h79.is_Char) {
                  unmatched105 = false;
                  {
                    RAST._IType _1999_rhsType;
                    RAST._IType _out321;
                    _out321 = (this).GenType(_1973_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1999_rhsType = _out321;
                    RAST._IExpr _2000_recursiveGen;
                    DCOMP._IOwnership _2001___v143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2002_recIdents;
                    RAST._IExpr _out322;
                    DCOMP._IOwnership _out323;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out324;
                    (this).GenExpr(_1971_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out322, out _out323, out _out324);
                    _2000_recursiveGen = _out322;
                    _2001___v143 = _out323;
                    _2002_recIdents = _out324;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_2000_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out325;
                    DCOMP._IOwnership _out326;
                    (this).FromOwned(r, expectedOwnership, out _out325, out _out326);
                    r = _out325;
                    resultingOwnership = _out326;
                    readIdents = _2002_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched105) {
          DAST._IType _06 = _source105.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h710 = _06.dtor_Primitive_a0;
            if (_h710.is_Char) {
              DAST._IType _16 = _source105.dtor__1;
              if (_16.is_Primitive) {
                DAST._IPrimitive _h711 = _16.dtor_Primitive_a0;
                if (_h711.is_Int) {
                  unmatched105 = false;
                  {
                    RAST._IType _2003_rhsType;
                    RAST._IType _out327;
                    _out327 = (this).GenType(_1972_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _2003_rhsType = _out327;
                    RAST._IExpr _2004_recursiveGen;
                    DCOMP._IOwnership _2005___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2006_recIdents;
                    RAST._IExpr _out328;
                    DCOMP._IOwnership _out329;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out330;
                    (this).GenExpr(_1971_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out328, out _out329, out _out330);
                    _2004_recursiveGen = _out328;
                    _2005___v144 = _out329;
                    _2006_recIdents = _out330;
                    r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1((_2004_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out331;
                    DCOMP._IOwnership _out332;
                    (this).FromOwned(r, expectedOwnership, out _out331, out _out332);
                    r = _out331;
                    resultingOwnership = _out332;
                    readIdents = _2006_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched105) {
          DAST._IType _07 = _source105.dtor__0;
          if (_07.is_Passthrough) {
            DAST._IType _17 = _source105.dtor__1;
            if (_17.is_Passthrough) {
              unmatched105 = false;
              {
                RAST._IExpr _2007_recursiveGen;
                DCOMP._IOwnership _2008___v147;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2009_recIdents;
                RAST._IExpr _out333;
                DCOMP._IOwnership _out334;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out335;
                (this).GenExpr(_1971_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out333, out _out334, out _out335);
                _2007_recursiveGen = _out333;
                _2008___v147 = _out334;
                _2009_recIdents = _out335;
                RAST._IType _2010_toTpeGen;
                RAST._IType _out336;
                _out336 = (this).GenType(_1973_toTpe, DCOMP.GenTypeContext.InBinding());
                _2010_toTpeGen = _out336;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_2007_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_2010_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out337;
                DCOMP._IOwnership _out338;
                (this).FromOwned(r, expectedOwnership, out _out337, out _out338);
                r = _out337;
                resultingOwnership = _out338;
                readIdents = _2009_recIdents;
              }
            }
          }
        }
        if (unmatched105) {
          unmatched105 = false;
          {
            RAST._IExpr _out339;
            DCOMP._IOwnership _out340;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out341;
            (this).GenExprConvertOther(e, selfIdent, env, expectedOwnership, out _out339, out _out340, out _out341);
            r = _out339;
            resultingOwnership = _out340;
            readIdents = _out341;
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
      Std.Wrappers._IOption<RAST._IType> _2011_tpe;
      _2011_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _2012_placeboOpt;
      _2012_placeboOpt = (((_2011_tpe).is_Some) ? (((_2011_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _2013_currentlyBorrowed;
      _2013_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _2014_noNeedOfClone;
      _2014_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_2012_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _2013_currentlyBorrowed = false;
        _2014_noNeedOfClone = true;
        _2011_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_2012_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_2013_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_2011_tpe).is_Some) && (((_2011_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _2015_needObjectFromRef;
        _2015_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source106 = (selfIdent).dtor_dafnyType;
          bool unmatched106 = true;
          if (unmatched106) {
            if (_source106.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source106.dtor_resolved;
              DAST._IResolvedTypeBase _2016_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _2017_attributes = resolved4.dtor_attributes;
              unmatched106 = false;
              return ((_2016_base).is_Class) || ((_2016_base).is_Trait);
            }
          }
          if (unmatched106) {
            unmatched106 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_2015_needObjectFromRef) {
          r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_2014_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_2014_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_2013_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_2011_tpe).is_Some) && (((_2011_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_2018_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_2018_attributes).UniqueElements, false, (((_exists_var_2) => {
        DAST._IAttribute _2019_attribute = (DAST._IAttribute)_exists_var_2;
        return ((_2018_attributes).Contains(_2019_attribute)) && ((((_2019_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_2019_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      Dafny.ISequence<DAST._IFormal> _2020_signature;
      _2020_signature = (((name).is_CallName) ? ((((((name).dtor_receiverArg).is_Some) && ((name).dtor_receiverAsArgument)) ? (Dafny.Sequence<DAST._IFormal>.Concat(Dafny.Sequence<DAST._IFormal>.FromElements(((name).dtor_receiverArg).dtor_value), ((name).dtor_signature))) : (((name).dtor_signature)))) : (Dafny.Sequence<DAST._IFormal>.FromElements()));
      BigInteger _hi38 = new BigInteger((args).Count);
      for (BigInteger _2021_i = BigInteger.Zero; _2021_i < _hi38; _2021_i++) {
        DCOMP._IOwnership _2022_argOwnership;
        _2022_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if ((_2021_i) < (new BigInteger((_2020_signature).Count))) {
          RAST._IType _2023_tpe;
          RAST._IType _out342;
          _out342 = (this).GenType(((_2020_signature).Select(_2021_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _2023_tpe = _out342;
          if ((_2023_tpe).CanReadWithoutClone()) {
            _2022_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _2024_argExpr;
        DCOMP._IOwnership _2025___v154;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2026_argIdents;
        RAST._IExpr _out343;
        DCOMP._IOwnership _out344;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out345;
        (this).GenExpr((args).Select(_2021_i), selfIdent, env, _2022_argOwnership, out _out343, out _out344, out _out345);
        _2024_argExpr = _out343;
        _2025___v154 = _out344;
        _2026_argIdents = _out345;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2024_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2026_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi39 = new BigInteger((typeArgs).Count);
      for (BigInteger _2027_typeI = BigInteger.Zero; _2027_typeI < _hi39; _2027_typeI++) {
        RAST._IType _2028_typeExpr;
        RAST._IType _out346;
        _out346 = (this).GenType((typeArgs).Select(_2027_typeI), DCOMP.GenTypeContext.@default());
        _2028_typeExpr = _out346;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2028_typeExpr));
      }
      DAST._ICallName _source107 = name;
      bool unmatched107 = true;
      if (unmatched107) {
        if (_source107.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _2029_nameIdent = _source107.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType1 = _source107.dtor_onType;
          if (onType1.is_Some) {
            DAST._IType value10 = onType1.dtor_value;
            if (value10.is_UserDefined) {
              DAST._IResolvedType _2030_resolvedType = value10.dtor_resolved;
              unmatched107 = false;
              if ((((_2030_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_2031_resolvedType, _2032_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.SingleValue<Dafny.ISequence<Dafny.Rune>>(_2032_nameIdent), true, (((_forall_var_8) => {
                Dafny.ISequence<Dafny.Rune> _2033_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                return !(((_2031_resolvedType).dtor_properMethods).Contains(_2033_m)) || (!object.Equals(_2033_m, _2032_nameIdent));
              }))))(_2030_resolvedType, _2029_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_2030_resolvedType, (_2029_nameIdent)), _2030_resolvedType));
              } else {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
              }
            }
          }
        }
      }
      if (unmatched107) {
        unmatched107 = false;
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
      if ((((((fullNameQualifier).is_Some) && ((selfIdent).is_ThisTyped)) && (((selfIdent).dtor_dafnyType).is_UserDefined)) && ((this).IsSameResolvedType(((selfIdent).dtor_dafnyType).dtor_resolved, (fullNameQualifier).dtor_value))) && (!((this).HasExternAttributeRenamingModule(((fullNameQualifier).dtor_value).dtor_attributes)))) {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    }
    public Dafny.ISequence<Dafny.Rune> GetMethodName(DAST._IExpression @on, DAST._ICallName name)
    {
      var _pat_let_tv200 = @on;
      DAST._ICallName _source108 = name;
      bool unmatched108 = true;
      if (unmatched108) {
        if (_source108.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _2034_ident = _source108.dtor_name;
          unmatched108 = false;
          if ((_pat_let_tv200).is_ExternCompanion) {
            return (_2034_ident);
          } else {
            return DCOMP.__default.escapeName(_2034_ident);
          }
        }
      }
      if (unmatched108) {
        bool disjunctiveMatch15 = false;
        if (_source108.is_MapBuilderAdd) {
          disjunctiveMatch15 = true;
        }
        if (_source108.is_SetBuilderAdd) {
          disjunctiveMatch15 = true;
        }
        if (disjunctiveMatch15) {
          unmatched108 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
        }
      }
      if (unmatched108) {
        bool disjunctiveMatch16 = false;
        disjunctiveMatch16 = true;
        disjunctiveMatch16 = true;
        if (disjunctiveMatch16) {
          unmatched108 = false;
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
      DAST._IExpression _source109 = e;
      bool unmatched109 = true;
      if (unmatched109) {
        if (_source109.is_Literal) {
          unmatched109 = false;
          RAST._IExpr _out347;
          DCOMP._IOwnership _out348;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out347, out _out348, out _out349);
          r = _out347;
          resultingOwnership = _out348;
          readIdents = _out349;
        }
      }
      if (unmatched109) {
        if (_source109.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _2035_name = _source109.dtor_name;
          unmatched109 = false;
          {
            RAST._IExpr _out350;
            DCOMP._IOwnership _out351;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out352;
            (this).GenIdent(DCOMP.__default.escapeVar(_2035_name), selfIdent, env, expectedOwnership, out _out350, out _out351, out _out352);
            r = _out350;
            resultingOwnership = _out351;
            readIdents = _out352;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_ExternCompanion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2036_path = _source109.dtor_ExternCompanion_a0;
          unmatched109 = false;
          {
            RAST._IExpr _out353;
            _out353 = DCOMP.COMP.GenPathExpr(_2036_path, false);
            r = _out353;
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
      if (unmatched109) {
        if (_source109.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2037_path = _source109.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _2038_typeArgs = _source109.dtor_typeArgs;
          unmatched109 = false;
          {
            RAST._IExpr _out356;
            _out356 = DCOMP.COMP.GenPathExpr(_2037_path, true);
            r = _out356;
            if ((new BigInteger((_2038_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _2039_typeExprs;
              _2039_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_2038_typeArgs).Count);
              for (BigInteger _2040_i = BigInteger.Zero; _2040_i < _hi40; _2040_i++) {
                RAST._IType _2041_typeExpr;
                RAST._IType _out357;
                _out357 = (this).GenType((_2038_typeArgs).Select(_2040_i), DCOMP.GenTypeContext.@default());
                _2041_typeExpr = _out357;
                _2039_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_2039_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2041_typeExpr));
              }
              r = (r).ApplyType(_2039_typeExprs);
            }
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out358;
              DCOMP._IOwnership _out359;
              (this).FromOwned(r, expectedOwnership, out _out358, out _out359);
              r = _out358;
              resultingOwnership = _out359;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_InitializationValue) {
          DAST._IType _2042_typ = _source109.dtor_typ;
          unmatched109 = false;
          {
            RAST._IType _2043_typExpr;
            RAST._IType _out360;
            _out360 = (this).GenType(_2042_typ, DCOMP.GenTypeContext.@default());
            _2043_typExpr = _out360;
            if ((_2043_typExpr).IsObjectOrPointer()) {
              r = (_2043_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_2043_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            }
            RAST._IExpr _out361;
            DCOMP._IOwnership _out362;
            (this).FromOwned(r, expectedOwnership, out _out361, out _out362);
            r = _out361;
            resultingOwnership = _out362;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _2044_values = _source109.dtor_Tuple_a0;
          unmatched109 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2045_exprs;
            _2045_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi41 = new BigInteger((_2044_values).Count);
            for (BigInteger _2046_i = BigInteger.Zero; _2046_i < _hi41; _2046_i++) {
              RAST._IExpr _2047_recursiveGen;
              DCOMP._IOwnership _2048___v164;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2049_recIdents;
              RAST._IExpr _out363;
              DCOMP._IOwnership _out364;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out365;
              (this).GenExpr((_2044_values).Select(_2046_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out363, out _out364, out _out365);
              _2047_recursiveGen = _out363;
              _2048___v164 = _out364;
              _2049_recIdents = _out365;
              _2045_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_2045_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2047_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2049_recIdents);
            }
            r = (((new BigInteger((_2044_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_2045_exprs)) : (RAST.__default.SystemTuple(_2045_exprs)));
            RAST._IExpr _out366;
            DCOMP._IOwnership _out367;
            (this).FromOwned(r, expectedOwnership, out _out366, out _out367);
            r = _out366;
            resultingOwnership = _out367;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2050_path = _source109.dtor_path;
          Dafny.ISequence<DAST._IType> _2051_typeArgs = _source109.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2052_args = _source109.dtor_args;
          unmatched109 = false;
          {
            RAST._IExpr _out368;
            _out368 = DCOMP.COMP.GenPathExpr(_2050_path, true);
            r = _out368;
            if ((new BigInteger((_2051_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _2053_typeExprs;
              _2053_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi42 = new BigInteger((_2051_typeArgs).Count);
              for (BigInteger _2054_i = BigInteger.Zero; _2054_i < _hi42; _2054_i++) {
                RAST._IType _2055_typeExpr;
                RAST._IType _out369;
                _out369 = (this).GenType((_2051_typeArgs).Select(_2054_i), DCOMP.GenTypeContext.@default());
                _2055_typeExpr = _out369;
                _2053_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_2053_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2055_typeExpr));
              }
              r = (r).ApplyType(_2053_typeExprs);
            }
            r = (r).FSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _2056_arguments;
            _2056_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi43 = new BigInteger((_2052_args).Count);
            for (BigInteger _2057_i = BigInteger.Zero; _2057_i < _hi43; _2057_i++) {
              RAST._IExpr _2058_recursiveGen;
              DCOMP._IOwnership _2059___v165;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2060_recIdents;
              RAST._IExpr _out370;
              DCOMP._IOwnership _out371;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out372;
              (this).GenExpr((_2052_args).Select(_2057_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out370, out _out371, out _out372);
              _2058_recursiveGen = _out370;
              _2059___v165 = _out371;
              _2060_recIdents = _out372;
              _2056_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2056_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2058_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2060_recIdents);
            }
            r = (r).Apply(_2056_arguments);
            RAST._IExpr _out373;
            DCOMP._IOwnership _out374;
            (this).FromOwned(r, expectedOwnership, out _out373, out _out374);
            r = _out373;
            resultingOwnership = _out374;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _2061_dims = _source109.dtor_dims;
          DAST._IType _2062_typ = _source109.dtor_typ;
          unmatched109 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_2061_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _2063_msg;
              _2063_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2063_msg);
              }
              r = RAST.Expr.create_RawExpr(_2063_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _2064_typeGen;
              RAST._IType _out375;
              _out375 = (this).GenType(_2062_typ, DCOMP.GenTypeContext.@default());
              _2064_typeGen = _out375;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _2065_dimExprs;
              _2065_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi44 = new BigInteger((_2061_dims).Count);
              for (BigInteger _2066_i = BigInteger.Zero; _2066_i < _hi44; _2066_i++) {
                RAST._IExpr _2067_recursiveGen;
                DCOMP._IOwnership _2068___v166;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2069_recIdents;
                RAST._IExpr _out376;
                DCOMP._IOwnership _out377;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out378;
                (this).GenExpr((_2061_dims).Select(_2066_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out376, out _out377, out _out378);
                _2067_recursiveGen = _out376;
                _2068___v166 = _out377;
                _2069_recIdents = _out378;
                _2065_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_2065_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_2067_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2069_recIdents);
              }
              if ((new BigInteger((_2061_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _2070_class__name;
                _2070_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_2061_dims).Count)));
                r = (((((RAST.__default.dafny__runtime).MSel(_2070_class__name)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2064_typeGen))).FSel((this).placebos__usize)).Apply(_2065_dimExprs);
              } else {
                r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2064_typeGen))).Apply(_2065_dimExprs);
              }
            }
            RAST._IExpr _out379;
            DCOMP._IOwnership _out380;
            (this).FromOwned(r, expectedOwnership, out _out379, out _out380);
            r = _out379;
            resultingOwnership = _out380;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_ArrayIndexToInt) {
          DAST._IExpression _2071_underlying = _source109.dtor_value;
          unmatched109 = false;
          {
            RAST._IExpr _2072_recursiveGen;
            DCOMP._IOwnership _2073___v167;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2074_recIdents;
            RAST._IExpr _out381;
            DCOMP._IOwnership _out382;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
            (this).GenExpr(_2071_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out381, out _out382, out _out383);
            _2072_recursiveGen = _out381;
            _2073___v167 = _out382;
            _2074_recIdents = _out383;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(_2072_recursiveGen);
            readIdents = _2074_recIdents;
            RAST._IExpr _out384;
            DCOMP._IOwnership _out385;
            (this).FromOwned(r, expectedOwnership, out _out384, out _out385);
            r = _out384;
            resultingOwnership = _out385;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_FinalizeNewArray) {
          DAST._IExpression _2075_underlying = _source109.dtor_value;
          DAST._IType _2076_typ = _source109.dtor_typ;
          unmatched109 = false;
          {
            RAST._IType _2077_tpe;
            RAST._IType _out386;
            _out386 = (this).GenType(_2076_typ, DCOMP.GenTypeContext.@default());
            _2077_tpe = _out386;
            RAST._IExpr _2078_recursiveGen;
            DCOMP._IOwnership _2079___v168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2080_recIdents;
            RAST._IExpr _out387;
            DCOMP._IOwnership _out388;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
            (this).GenExpr(_2075_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out387, out _out388, out _out389);
            _2078_recursiveGen = _out387;
            _2079___v168 = _out388;
            _2080_recIdents = _out389;
            readIdents = _2080_recIdents;
            if ((_2077_tpe).IsObjectOrPointer()) {
              RAST._IType _2081_t;
              _2081_t = (_2077_tpe).ObjectOrPointerUnderlying();
              if ((_2081_t).is_Array) {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).array__construct)).Apply1(_2078_recursiveGen);
              } else if ((_2081_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _2082_c;
                _2082_c = (_2081_t).MultiArrayClass();
                r = ((((RAST.__default.dafny__runtime).MSel(_2082_c)).AsExpr()).FSel((this).array__construct)).Apply1(_2078_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_2077_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_2077_tpe)._ToString(DCOMP.__default.IND)));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            }
            RAST._IExpr _out390;
            DCOMP._IOwnership _out391;
            (this).FromOwned(r, expectedOwnership, out _out390, out _out391);
            r = _out390;
            resultingOwnership = _out391;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_DatatypeValue) {
          DAST._IResolvedType _2083_datatypeType = _source109.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _2084_typeArgs = _source109.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _2085_variant = _source109.dtor_variant;
          bool _2086_isCo = _source109.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2087_values = _source109.dtor_contents;
          unmatched109 = false;
          {
            RAST._IExpr _out392;
            _out392 = DCOMP.COMP.GenPathExpr((_2083_datatypeType).dtor_path, true);
            r = _out392;
            Dafny.ISequence<RAST._IType> _2088_genTypeArgs;
            _2088_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi45 = new BigInteger((_2084_typeArgs).Count);
            for (BigInteger _2089_i = BigInteger.Zero; _2089_i < _hi45; _2089_i++) {
              RAST._IType _2090_typeExpr;
              RAST._IType _out393;
              _out393 = (this).GenType((_2084_typeArgs).Select(_2089_i), DCOMP.GenTypeContext.@default());
              _2090_typeExpr = _out393;
              _2088_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_2088_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_2090_typeExpr));
            }
            if ((new BigInteger((_2084_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_2088_genTypeArgs);
            }
            r = (r).FSel(DCOMP.__default.escapeName(_2085_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _2091_assignments;
            _2091_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi46 = new BigInteger((_2087_values).Count);
            for (BigInteger _2092_i = BigInteger.Zero; _2092_i < _hi46; _2092_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs69 = (_2087_values).Select(_2092_i);
              Dafny.ISequence<Dafny.Rune> _2093_name = _let_tmp_rhs69.dtor__0;
              DAST._IExpression _2094_value = _let_tmp_rhs69.dtor__1;
              if (_2086_isCo) {
                RAST._IExpr _2095_recursiveGen;
                DCOMP._IOwnership _2096___v169;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2097_recIdents;
                RAST._IExpr _out394;
                DCOMP._IOwnership _out395;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out396;
                (this).GenExpr(_2094_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out394, out _out395, out _out396);
                _2095_recursiveGen = _out394;
                _2096___v169 = _out395;
                _2097_recIdents = _out396;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2097_recIdents);
                Dafny.ISequence<Dafny.Rune> _2098_allReadCloned;
                _2098_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_2097_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _2099_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2097_recIdents).Elements) {
                    _2099_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                    if ((_2097_recIdents).Contains(_2099_next)) {
                      goto after__ASSIGN_SUCH_THAT_3;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4728)");
                after__ASSIGN_SUCH_THAT_3: ;
                  _2098_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2098_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _2099_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2099_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _2097_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2097_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2099_next));
                }
                Dafny.ISequence<Dafny.Rune> _2100_wasAssigned;
                _2100_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _2098_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_2095_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _2091_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2091_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_2093_name), RAST.Expr.create_RawExpr(_2100_wasAssigned))));
              } else {
                RAST._IExpr _2101_recursiveGen;
                DCOMP._IOwnership _2102___v170;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2103_recIdents;
                RAST._IExpr _out397;
                DCOMP._IOwnership _out398;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
                (this).GenExpr(_2094_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out397, out _out398, out _out399);
                _2101_recursiveGen = _out397;
                _2102___v170 = _out398;
                _2103_recIdents = _out399;
                _2091_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2091_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_2093_name), _2101_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2103_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _2091_assignments);
            if ((this).IsRcWrapped((_2083_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out400;
            DCOMP._IOwnership _out401;
            (this).FromOwned(r, expectedOwnership, out _out400, out _out401);
            r = _out400;
            resultingOwnership = _out401;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Convert) {
          unmatched109 = false;
          {
            RAST._IExpr _out402;
            DCOMP._IOwnership _out403;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out404;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out402, out _out403, out _out404);
            r = _out402;
            resultingOwnership = _out403;
            readIdents = _out404;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SeqConstruct) {
          DAST._IExpression _2104_length = _source109.dtor_length;
          DAST._IExpression _2105_expr = _source109.dtor_elem;
          unmatched109 = false;
          {
            RAST._IExpr _2106_recursiveGen;
            DCOMP._IOwnership _2107___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2108_recIdents;
            RAST._IExpr _out405;
            DCOMP._IOwnership _out406;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out407;
            (this).GenExpr(_2105_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out405, out _out406, out _out407);
            _2106_recursiveGen = _out405;
            _2107___v174 = _out406;
            _2108_recIdents = _out407;
            RAST._IExpr _2109_lengthGen;
            DCOMP._IOwnership _2110___v175;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2111_lengthIdents;
            RAST._IExpr _out408;
            DCOMP._IOwnership _out409;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out410;
            (this).GenExpr(_2104_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out408, out _out409, out _out410);
            _2109_lengthGen = _out408;
            _2110___v175 = _out409;
            _2111_lengthIdents = _out410;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_2106_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_2109_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2108_recIdents, _2111_lengthIdents);
            RAST._IExpr _out411;
            DCOMP._IOwnership _out412;
            (this).FromOwned(r, expectedOwnership, out _out411, out _out412);
            r = _out411;
            resultingOwnership = _out412;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _2112_exprs = _source109.dtor_elements;
          DAST._IType _2113_typ = _source109.dtor_typ;
          unmatched109 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _2114_genTpe;
            RAST._IType _out413;
            _out413 = (this).GenType(_2113_typ, DCOMP.GenTypeContext.@default());
            _2114_genTpe = _out413;
            BigInteger _2115_i;
            _2115_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2116_args;
            _2116_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2115_i) < (new BigInteger((_2112_exprs).Count))) {
              RAST._IExpr _2117_recursiveGen;
              DCOMP._IOwnership _2118___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2119_recIdents;
              RAST._IExpr _out414;
              DCOMP._IOwnership _out415;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out416;
              (this).GenExpr((_2112_exprs).Select(_2115_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out414, out _out415, out _out416);
              _2117_recursiveGen = _out414;
              _2118___v176 = _out415;
              _2119_recIdents = _out416;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2119_recIdents);
              _2116_args = Dafny.Sequence<RAST._IExpr>.Concat(_2116_args, Dafny.Sequence<RAST._IExpr>.FromElements(_2117_recursiveGen));
              _2115_i = (_2115_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).AsExpr()).Apply(_2116_args);
            if ((new BigInteger((_2116_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType()).Apply1(_2114_genTpe));
            }
            RAST._IExpr _out417;
            DCOMP._IOwnership _out418;
            (this).FromOwned(r, expectedOwnership, out _out417, out _out418);
            r = _out417;
            resultingOwnership = _out418;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _2120_exprs = _source109.dtor_elements;
          unmatched109 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2121_generatedValues;
            _2121_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2122_i;
            _2122_i = BigInteger.Zero;
            while ((_2122_i) < (new BigInteger((_2120_exprs).Count))) {
              RAST._IExpr _2123_recursiveGen;
              DCOMP._IOwnership _2124___v177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2125_recIdents;
              RAST._IExpr _out419;
              DCOMP._IOwnership _out420;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out421;
              (this).GenExpr((_2120_exprs).Select(_2122_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out419, out _out420, out _out421);
              _2123_recursiveGen = _out419;
              _2124___v177 = _out420;
              _2125_recIdents = _out421;
              _2121_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2121_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2123_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2125_recIdents);
              _2122_i = (_2122_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).AsExpr()).Apply(_2121_generatedValues);
            RAST._IExpr _out422;
            DCOMP._IOwnership _out423;
            (this).FromOwned(r, expectedOwnership, out _out422, out _out423);
            r = _out422;
            resultingOwnership = _out423;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _2126_exprs = _source109.dtor_elements;
          unmatched109 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2127_generatedValues;
            _2127_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2128_i;
            _2128_i = BigInteger.Zero;
            while ((_2128_i) < (new BigInteger((_2126_exprs).Count))) {
              RAST._IExpr _2129_recursiveGen;
              DCOMP._IOwnership _2130___v178;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2131_recIdents;
              RAST._IExpr _out424;
              DCOMP._IOwnership _out425;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out426;
              (this).GenExpr((_2126_exprs).Select(_2128_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out424, out _out425, out _out426);
              _2129_recursiveGen = _out424;
              _2130___v178 = _out425;
              _2131_recIdents = _out426;
              _2127_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2127_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2129_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2131_recIdents);
              _2128_i = (_2128_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).AsExpr()).Apply(_2127_generatedValues);
            RAST._IExpr _out427;
            DCOMP._IOwnership _out428;
            (this).FromOwned(r, expectedOwnership, out _out427, out _out428);
            r = _out427;
            resultingOwnership = _out428;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_ToMultiset) {
          DAST._IExpression _2132_expr = _source109.dtor_ToMultiset_a0;
          unmatched109 = false;
          {
            RAST._IExpr _2133_recursiveGen;
            DCOMP._IOwnership _2134___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2135_recIdents;
            RAST._IExpr _out429;
            DCOMP._IOwnership _out430;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out431;
            (this).GenExpr(_2132_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out429, out _out430, out _out431);
            _2133_recursiveGen = _out429;
            _2134___v179 = _out430;
            _2135_recIdents = _out431;
            r = ((_2133_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2135_recIdents;
            RAST._IExpr _out432;
            DCOMP._IOwnership _out433;
            (this).FromOwned(r, expectedOwnership, out _out432, out _out433);
            r = _out432;
            resultingOwnership = _out433;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2136_mapElems = _source109.dtor_mapElems;
          unmatched109 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _2137_generatedValues;
            _2137_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2138_i;
            _2138_i = BigInteger.Zero;
            while ((_2138_i) < (new BigInteger((_2136_mapElems).Count))) {
              RAST._IExpr _2139_recursiveGenKey;
              DCOMP._IOwnership _2140___v180;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2141_recIdentsKey;
              RAST._IExpr _out434;
              DCOMP._IOwnership _out435;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
              (this).GenExpr(((_2136_mapElems).Select(_2138_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out434, out _out435, out _out436);
              _2139_recursiveGenKey = _out434;
              _2140___v180 = _out435;
              _2141_recIdentsKey = _out436;
              RAST._IExpr _2142_recursiveGenValue;
              DCOMP._IOwnership _2143___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2144_recIdentsValue;
              RAST._IExpr _out437;
              DCOMP._IOwnership _out438;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
              (this).GenExpr(((_2136_mapElems).Select(_2138_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out437, out _out438, out _out439);
              _2142_recursiveGenValue = _out437;
              _2143___v181 = _out438;
              _2144_recIdentsValue = _out439;
              _2137_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_2137_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_2139_recursiveGenKey, _2142_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2141_recIdentsKey), _2144_recIdentsValue);
              _2138_i = (_2138_i) + (BigInteger.One);
            }
            _2138_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2145_arguments;
            _2145_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2138_i) < (new BigInteger((_2137_generatedValues).Count))) {
              RAST._IExpr _2146_genKey;
              _2146_genKey = ((_2137_generatedValues).Select(_2138_i)).dtor__0;
              RAST._IExpr _2147_genValue;
              _2147_genValue = ((_2137_generatedValues).Select(_2138_i)).dtor__1;
              _2145_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2145_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _2146_genKey, _2147_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _2138_i = (_2138_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).AsExpr()).Apply(_2145_arguments);
            RAST._IExpr _out440;
            DCOMP._IOwnership _out441;
            (this).FromOwned(r, expectedOwnership, out _out440, out _out441);
            r = _out440;
            resultingOwnership = _out441;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SeqUpdate) {
          DAST._IExpression _2148_expr = _source109.dtor_expr;
          DAST._IExpression _2149_index = _source109.dtor_indexExpr;
          DAST._IExpression _2150_value = _source109.dtor_value;
          unmatched109 = false;
          {
            RAST._IExpr _2151_exprR;
            DCOMP._IOwnership _2152___v182;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2153_exprIdents;
            RAST._IExpr _out442;
            DCOMP._IOwnership _out443;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out444;
            (this).GenExpr(_2148_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out442, out _out443, out _out444);
            _2151_exprR = _out442;
            _2152___v182 = _out443;
            _2153_exprIdents = _out444;
            RAST._IExpr _2154_indexR;
            DCOMP._IOwnership _2155_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2156_indexIdents;
            RAST._IExpr _out445;
            DCOMP._IOwnership _out446;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
            (this).GenExpr(_2149_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out445, out _out446, out _out447);
            _2154_indexR = _out445;
            _2155_indexOwnership = _out446;
            _2156_indexIdents = _out447;
            RAST._IExpr _2157_valueR;
            DCOMP._IOwnership _2158_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2159_valueIdents;
            RAST._IExpr _out448;
            DCOMP._IOwnership _out449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out450;
            (this).GenExpr(_2150_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out448, out _out449, out _out450);
            _2157_valueR = _out448;
            _2158_valueOwnership = _out449;
            _2159_valueIdents = _out450;
            r = ((_2151_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2154_indexR, _2157_valueR));
            RAST._IExpr _out451;
            DCOMP._IOwnership _out452;
            (this).FromOwned(r, expectedOwnership, out _out451, out _out452);
            r = _out451;
            resultingOwnership = _out452;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2153_exprIdents, _2156_indexIdents), _2159_valueIdents);
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapUpdate) {
          DAST._IExpression _2160_expr = _source109.dtor_expr;
          DAST._IExpression _2161_index = _source109.dtor_indexExpr;
          DAST._IExpression _2162_value = _source109.dtor_value;
          unmatched109 = false;
          {
            RAST._IExpr _2163_exprR;
            DCOMP._IOwnership _2164___v183;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2165_exprIdents;
            RAST._IExpr _out453;
            DCOMP._IOwnership _out454;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out455;
            (this).GenExpr(_2160_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out453, out _out454, out _out455);
            _2163_exprR = _out453;
            _2164___v183 = _out454;
            _2165_exprIdents = _out455;
            RAST._IExpr _2166_indexR;
            DCOMP._IOwnership _2167_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2168_indexIdents;
            RAST._IExpr _out456;
            DCOMP._IOwnership _out457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out458;
            (this).GenExpr(_2161_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out456, out _out457, out _out458);
            _2166_indexR = _out456;
            _2167_indexOwnership = _out457;
            _2168_indexIdents = _out458;
            RAST._IExpr _2169_valueR;
            DCOMP._IOwnership _2170_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2171_valueIdents;
            RAST._IExpr _out459;
            DCOMP._IOwnership _out460;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out461;
            (this).GenExpr(_2162_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out459, out _out460, out _out461);
            _2169_valueR = _out459;
            _2170_valueOwnership = _out460;
            _2171_valueIdents = _out461;
            r = ((_2163_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2166_indexR, _2169_valueR));
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            (this).FromOwned(r, expectedOwnership, out _out462, out _out463);
            r = _out462;
            resultingOwnership = _out463;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2165_exprIdents, _2168_indexIdents), _2171_valueIdents);
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_This) {
          unmatched109 = false;
          {
            DCOMP._ISelfInfo _source110 = selfIdent;
            bool unmatched110 = true;
            if (unmatched110) {
              if (_source110.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _2172_id = _source110.dtor_rSelfName;
                DAST._IType _2173_dafnyType = _source110.dtor_dafnyType;
                unmatched110 = false;
                {
                  RAST._IExpr _out464;
                  DCOMP._IOwnership _out465;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
                  (this).GenIdent(_2172_id, selfIdent, env, expectedOwnership, out _out464, out _out465, out _out466);
                  r = _out464;
                  resultingOwnership = _out465;
                  readIdents = _out466;
                }
              }
            }
            if (unmatched110) {
              DCOMP._ISelfInfo _2174_None = _source110;
              unmatched110 = false;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out467;
                DCOMP._IOwnership _out468;
                (this).FromOwned(r, expectedOwnership, out _out467, out _out468);
                r = _out467;
                resultingOwnership = _out468;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Ite) {
          DAST._IExpression _2175_cond = _source109.dtor_cond;
          DAST._IExpression _2176_t = _source109.dtor_thn;
          DAST._IExpression _2177_f = _source109.dtor_els;
          unmatched109 = false;
          {
            RAST._IExpr _2178_cond;
            DCOMP._IOwnership _2179___v184;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2180_recIdentsCond;
            RAST._IExpr _out469;
            DCOMP._IOwnership _out470;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out471;
            (this).GenExpr(_2175_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out469, out _out470, out _out471);
            _2178_cond = _out469;
            _2179___v184 = _out470;
            _2180_recIdentsCond = _out471;
            RAST._IExpr _2181_fExpr;
            DCOMP._IOwnership _2182_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2183_recIdentsF;
            RAST._IExpr _out472;
            DCOMP._IOwnership _out473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
            (this).GenExpr(_2177_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out472, out _out473, out _out474);
            _2181_fExpr = _out472;
            _2182_fOwned = _out473;
            _2183_recIdentsF = _out474;
            RAST._IExpr _2184_tExpr;
            DCOMP._IOwnership _2185___v185;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2186_recIdentsT;
            RAST._IExpr _out475;
            DCOMP._IOwnership _out476;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out477;
            (this).GenExpr(_2176_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out475, out _out476, out _out477);
            _2184_tExpr = _out475;
            _2185___v185 = _out476;
            _2186_recIdentsT = _out477;
            r = RAST.Expr.create_IfExpr(_2178_cond, _2184_tExpr, _2181_fExpr);
            RAST._IExpr _out478;
            DCOMP._IOwnership _out479;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out478, out _out479);
            r = _out478;
            resultingOwnership = _out479;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2180_recIdentsCond, _2186_recIdentsT), _2183_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source109.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _2187_e = _source109.dtor_expr;
            DAST.Format._IUnaryOpFormat _2188_format = _source109.dtor_format1;
            unmatched109 = false;
            {
              RAST._IExpr _2189_recursiveGen;
              DCOMP._IOwnership _2190___v186;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2191_recIdents;
              RAST._IExpr _out480;
              DCOMP._IOwnership _out481;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out482;
              (this).GenExpr(_2187_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out480, out _out481, out _out482);
              _2189_recursiveGen = _out480;
              _2190___v186 = _out481;
              _2191_recIdents = _out482;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _2189_recursiveGen, _2188_format);
              RAST._IExpr _out483;
              DCOMP._IOwnership _out484;
              (this).FromOwned(r, expectedOwnership, out _out483, out _out484);
              r = _out483;
              resultingOwnership = _out484;
              readIdents = _2191_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source109.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _2192_e = _source109.dtor_expr;
            DAST.Format._IUnaryOpFormat _2193_format = _source109.dtor_format1;
            unmatched109 = false;
            {
              RAST._IExpr _2194_recursiveGen;
              DCOMP._IOwnership _2195___v187;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2196_recIdents;
              RAST._IExpr _out485;
              DCOMP._IOwnership _out486;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out487;
              (this).GenExpr(_2192_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out485, out _out486, out _out487);
              _2194_recursiveGen = _out485;
              _2195___v187 = _out486;
              _2196_recIdents = _out487;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _2194_recursiveGen, _2193_format);
              RAST._IExpr _out488;
              DCOMP._IOwnership _out489;
              (this).FromOwned(r, expectedOwnership, out _out488, out _out489);
              r = _out488;
              resultingOwnership = _out489;
              readIdents = _2196_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source109.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _2197_e = _source109.dtor_expr;
            DAST.Format._IUnaryOpFormat _2198_format = _source109.dtor_format1;
            unmatched109 = false;
            {
              RAST._IExpr _2199_recursiveGen;
              DCOMP._IOwnership _2200_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2201_recIdents;
              RAST._IExpr _out490;
              DCOMP._IOwnership _out491;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out492;
              (this).GenExpr(_2197_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out490, out _out491, out _out492);
              _2199_recursiveGen = _out490;
              _2200_recOwned = _out491;
              _2201_recIdents = _out492;
              r = ((_2199_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out493;
              DCOMP._IOwnership _out494;
              (this).FromOwned(r, expectedOwnership, out _out493, out _out494);
              r = _out493;
              resultingOwnership = _out494;
              readIdents = _2201_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_BinOp) {
          unmatched109 = false;
          RAST._IExpr _out495;
          DCOMP._IOwnership _out496;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out497;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out495, out _out496, out _out497);
          r = _out495;
          resultingOwnership = _out496;
          readIdents = _out497;
        }
      }
      if (unmatched109) {
        if (_source109.is_ArrayLen) {
          DAST._IExpression _2202_expr = _source109.dtor_expr;
          DAST._IType _2203_exprType = _source109.dtor_exprType;
          BigInteger _2204_dim = _source109.dtor_dim;
          bool _2205_native = _source109.dtor_native;
          unmatched109 = false;
          {
            RAST._IExpr _2206_recursiveGen;
            DCOMP._IOwnership _2207___v192;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2208_recIdents;
            RAST._IExpr _out498;
            DCOMP._IOwnership _out499;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
            (this).GenExpr(_2202_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out498, out _out499, out _out500);
            _2206_recursiveGen = _out498;
            _2207___v192 = _out499;
            _2208_recIdents = _out500;
            RAST._IType _2209_arrayType;
            RAST._IType _out501;
            _out501 = (this).GenType(_2203_exprType, DCOMP.GenTypeContext.@default());
            _2209_arrayType = _out501;
            if (!((_2209_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2210_msg;
              _2210_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2209_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2210_msg);
              r = RAST.Expr.create_RawExpr(_2210_msg);
            } else {
              RAST._IType _2211_underlying;
              _2211_underlying = (_2209_arrayType).ObjectOrPointerUnderlying();
              if (((_2204_dim).Sign == 0) && ((_2211_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2206_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2204_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2206_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_2206_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_2204_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_2205_native)) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(r);
              }
            }
            RAST._IExpr _out502;
            DCOMP._IOwnership _out503;
            (this).FromOwned(r, expectedOwnership, out _out502, out _out503);
            r = _out502;
            resultingOwnership = _out503;
            readIdents = _2208_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapKeys) {
          DAST._IExpression _2212_expr = _source109.dtor_expr;
          unmatched109 = false;
          {
            RAST._IExpr _2213_recursiveGen;
            DCOMP._IOwnership _2214___v193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2215_recIdents;
            RAST._IExpr _out504;
            DCOMP._IOwnership _out505;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out506;
            (this).GenExpr(_2212_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out504, out _out505, out _out506);
            _2213_recursiveGen = _out504;
            _2214___v193 = _out505;
            _2215_recIdents = _out506;
            readIdents = _2215_recIdents;
            r = ((_2213_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out507;
            DCOMP._IOwnership _out508;
            (this).FromOwned(r, expectedOwnership, out _out507, out _out508);
            r = _out507;
            resultingOwnership = _out508;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapValues) {
          DAST._IExpression _2216_expr = _source109.dtor_expr;
          unmatched109 = false;
          {
            RAST._IExpr _2217_recursiveGen;
            DCOMP._IOwnership _2218___v194;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2219_recIdents;
            RAST._IExpr _out509;
            DCOMP._IOwnership _out510;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out511;
            (this).GenExpr(_2216_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out509, out _out510, out _out511);
            _2217_recursiveGen = _out509;
            _2218___v194 = _out510;
            _2219_recIdents = _out511;
            readIdents = _2219_recIdents;
            r = ((_2217_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out512;
            DCOMP._IOwnership _out513;
            (this).FromOwned(r, expectedOwnership, out _out512, out _out513);
            r = _out512;
            resultingOwnership = _out513;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapItems) {
          DAST._IExpression _2220_expr = _source109.dtor_expr;
          unmatched109 = false;
          {
            RAST._IExpr _2221_recursiveGen;
            DCOMP._IOwnership _2222___v195;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2223_recIdents;
            RAST._IExpr _out514;
            DCOMP._IOwnership _out515;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out516;
            (this).GenExpr(_2220_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out514, out _out515, out _out516);
            _2221_recursiveGen = _out514;
            _2222___v195 = _out515;
            _2223_recIdents = _out516;
            readIdents = _2223_recIdents;
            r = ((_2221_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("items"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out517;
            DCOMP._IOwnership _out518;
            (this).FromOwned(r, expectedOwnership, out _out517, out _out518);
            r = _out517;
            resultingOwnership = _out518;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SelectFn) {
          DAST._IExpression _2224_on = _source109.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2225_field = _source109.dtor_field;
          bool _2226_isDatatype = _source109.dtor_onDatatype;
          bool _2227_isStatic = _source109.dtor_isStatic;
          bool _2228_isConstant = _source109.dtor_isConstant;
          Dafny.ISequence<DAST._IType> _2229_arguments = _source109.dtor_arguments;
          unmatched109 = false;
          {
            RAST._IExpr _2230_onExpr;
            DCOMP._IOwnership _2231_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2232_recIdents;
            RAST._IExpr _out519;
            DCOMP._IOwnership _out520;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
            (this).GenExpr(_2224_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out519, out _out520, out _out521);
            _2230_onExpr = _out519;
            _2231_onOwned = _out520;
            _2232_recIdents = _out521;
            Dafny.ISequence<Dafny.Rune> _2233_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2234_onString;
            _2234_onString = (_2230_onExpr)._ToString(DCOMP.__default.IND);
            if (_2227_isStatic) {
              DCOMP._IEnvironment _2235_lEnv;
              _2235_lEnv = env;
              Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>> _2236_args;
              _2236_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements();
              _2233_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|");
              BigInteger _hi47 = new BigInteger((_2229_arguments).Count);
              for (BigInteger _2237_i = BigInteger.Zero; _2237_i < _hi47; _2237_i++) {
                if ((_2237_i).Sign == 1) {
                  _2233_s = Dafny.Sequence<Dafny.Rune>.Concat(_2233_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                RAST._IType _2238_ty;
                RAST._IType _out522;
                _out522 = (this).GenType((_2229_arguments).Select(_2237_i), DCOMP.GenTypeContext.@default());
                _2238_ty = _out522;
                RAST._IType _2239_bTy;
                _2239_bTy = RAST.Type.create_Borrowed(_2238_ty);
                Dafny.ISequence<Dafny.Rune> _2240_name;
                _2240_name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), Std.Strings.__default.OfInt(_2237_i));
                _2235_lEnv = (_2235_lEnv).AddAssigned(_2240_name, _2239_bTy);
                _2236_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.Concat(_2236_args, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>.create(_2240_name, _2238_ty)));
                _2233_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2233_s, _2240_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_2239_bTy)._ToString(DCOMP.__default.IND));
              }
              _2233_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2233_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| ")), _2234_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeVar(_2225_field)), ((_2228_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("));
              BigInteger _hi48 = new BigInteger((_2236_args).Count);
              for (BigInteger _2241_i = BigInteger.Zero; _2241_i < _hi48; _2241_i++) {
                if ((_2241_i).Sign == 1) {
                  _2233_s = Dafny.Sequence<Dafny.Rune>.Concat(_2233_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType> _let_tmp_rhs70 = (_2236_args).Select(_2241_i);
                Dafny.ISequence<Dafny.Rune> _2242_name = _let_tmp_rhs70.dtor__0;
                RAST._IType _2243_ty = _let_tmp_rhs70.dtor__1;
                RAST._IExpr _2244_rIdent;
                DCOMP._IOwnership _2245___v196;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2246___v197;
                RAST._IExpr _out523;
                DCOMP._IOwnership _out524;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
                (this).GenIdent(_2242_name, selfIdent, _2235_lEnv, (((_2243_ty).CanReadWithoutClone()) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed())), out _out523, out _out524, out _out525);
                _2244_rIdent = _out523;
                _2245___v196 = _out524;
                _2246___v197 = _out525;
                _2233_s = Dafny.Sequence<Dafny.Rune>.Concat(_2233_s, (_2244_rIdent)._ToString(DCOMP.__default.IND));
              }
              _2233_s = Dafny.Sequence<Dafny.Rune>.Concat(_2233_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            } else {
              _2233_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2233_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2233_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2234_onString), ((object.Equals(_2231_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2247_args;
              _2247_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2248_i;
              _2248_i = BigInteger.Zero;
              while ((_2248_i) < (new BigInteger((_2229_arguments).Count))) {
                if ((_2248_i).Sign == 1) {
                  _2247_args = Dafny.Sequence<Dafny.Rune>.Concat(_2247_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2247_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2247_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2248_i));
                _2248_i = (_2248_i) + (BigInteger.One);
              }
              _2233_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2233_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2247_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2233_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2233_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeVar(_2225_field)), ((_2228_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2247_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2233_s = Dafny.Sequence<Dafny.Rune>.Concat(_2233_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2233_s = Dafny.Sequence<Dafny.Rune>.Concat(_2233_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2249_typeShape;
            _2249_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2250_i;
            _2250_i = BigInteger.Zero;
            while ((_2250_i) < (new BigInteger((_2229_arguments).Count))) {
              if ((_2250_i).Sign == 1) {
                _2249_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2249_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2249_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2249_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2250_i = (_2250_i) + (BigInteger.One);
            }
            _2249_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2249_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2233_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2233_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2249_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2233_s);
            RAST._IExpr _out526;
            DCOMP._IOwnership _out527;
            (this).FromOwned(r, expectedOwnership, out _out526, out _out527);
            r = _out526;
            resultingOwnership = _out527;
            readIdents = _2232_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Select) {
          DAST._IExpression _2251_on = _source109.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2252_field = _source109.dtor_field;
          bool _2253_isConstant = _source109.dtor_isConstant;
          bool _2254_isDatatype = _source109.dtor_onDatatype;
          DAST._IType _2255_fieldType = _source109.dtor_fieldType;
          unmatched109 = false;
          {
            if (((_2251_on).is_Companion) || ((_2251_on).is_ExternCompanion)) {
              RAST._IExpr _2256_onExpr;
              DCOMP._IOwnership _2257_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2258_recIdents;
              RAST._IExpr _out528;
              DCOMP._IOwnership _out529;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
              (this).GenExpr(_2251_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out528, out _out529, out _out530);
              _2256_onExpr = _out528;
              _2257_onOwned = _out529;
              _2258_recIdents = _out530;
              r = ((_2256_onExpr).FSel(DCOMP.__default.escapeVar(_2252_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out531;
              DCOMP._IOwnership _out532;
              (this).FromOwned(r, expectedOwnership, out _out531, out _out532);
              r = _out531;
              resultingOwnership = _out532;
              readIdents = _2258_recIdents;
              return ;
            } else if (_2254_isDatatype) {
              RAST._IExpr _2259_onExpr;
              DCOMP._IOwnership _2260_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2261_recIdents;
              RAST._IExpr _out533;
              DCOMP._IOwnership _out534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
              (this).GenExpr(_2251_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out533, out _out534, out _out535);
              _2259_onExpr = _out533;
              _2260_onOwned = _out534;
              _2261_recIdents = _out535;
              r = ((_2259_onExpr).Sel(DCOMP.__default.escapeVar(_2252_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2262_typ;
              RAST._IType _out536;
              _out536 = (this).GenType(_2255_fieldType, DCOMP.GenTypeContext.@default());
              _2262_typ = _out536;
              RAST._IExpr _out537;
              DCOMP._IOwnership _out538;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out537, out _out538);
              r = _out537;
              resultingOwnership = _out538;
              readIdents = _2261_recIdents;
            } else {
              RAST._IExpr _2263_onExpr;
              DCOMP._IOwnership _2264_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2265_recIdents;
              RAST._IExpr _out539;
              DCOMP._IOwnership _out540;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
              (this).GenExpr(_2251_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out539, out _out540, out _out541);
              _2263_onExpr = _out539;
              _2264_onOwned = _out540;
              _2265_recIdents = _out541;
              r = _2263_onExpr;
              if (!object.Equals(_2263_onExpr, RAST.__default.self)) {
                RAST._IExpr _source111 = _2263_onExpr;
                bool unmatched111 = true;
                if (unmatched111) {
                  if (_source111.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source111.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source111.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name8 = underlying5.dtor_name;
                        if (object.Equals(name8, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          unmatched111 = false;
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                        }
                      }
                    }
                  }
                }
                if (unmatched111) {
                  unmatched111 = false;
                }
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeVar(_2252_field));
              if (_2253_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out542;
              DCOMP._IOwnership _out543;
              (this).FromOwned(r, expectedOwnership, out _out542, out _out543);
              r = _out542;
              resultingOwnership = _out543;
              readIdents = _2265_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Index) {
          DAST._IExpression _2266_on = _source109.dtor_expr;
          DAST._ICollKind _2267_collKind = _source109.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2268_indices = _source109.dtor_indices;
          unmatched109 = false;
          {
            RAST._IExpr _2269_onExpr;
            DCOMP._IOwnership _2270_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2271_recIdents;
            RAST._IExpr _out544;
            DCOMP._IOwnership _out545;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out546;
            (this).GenExpr(_2266_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out544, out _out545, out _out546);
            _2269_onExpr = _out544;
            _2270_onOwned = _out545;
            _2271_recIdents = _out546;
            readIdents = _2271_recIdents;
            r = _2269_onExpr;
            bool _2272_hadArray;
            _2272_hadArray = false;
            if (object.Equals(_2267_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2272_hadArray = true;
              if ((new BigInteger((_2268_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi49 = new BigInteger((_2268_indices).Count);
            for (BigInteger _2273_i = BigInteger.Zero; _2273_i < _hi49; _2273_i++) {
              if (object.Equals(_2267_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2274_idx;
                DCOMP._IOwnership _2275_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2276_recIdentsIdx;
                RAST._IExpr _out547;
                DCOMP._IOwnership _out548;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
                (this).GenExpr((_2268_indices).Select(_2273_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out547, out _out548, out _out549);
                _2274_idx = _out547;
                _2275_idxOwned = _out548;
                _2276_recIdentsIdx = _out549;
                _2274_idx = RAST.__default.IntoUsize(_2274_idx);
                r = RAST.Expr.create_SelectIndex(r, _2274_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2276_recIdentsIdx);
              } else {
                RAST._IExpr _2277_idx;
                DCOMP._IOwnership _2278_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2279_recIdentsIdx;
                RAST._IExpr _out550;
                DCOMP._IOwnership _out551;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
                (this).GenExpr((_2268_indices).Select(_2273_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out550, out _out551, out _out552);
                _2277_idx = _out550;
                _2278_idxOwned = _out551;
                _2279_recIdentsIdx = _out552;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2277_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2279_recIdentsIdx);
              }
            }
            if (_2272_hadArray) {
              r = (r).Clone();
            }
            RAST._IExpr _out553;
            DCOMP._IOwnership _out554;
            (this).FromOwned(r, expectedOwnership, out _out553, out _out554);
            r = _out553;
            resultingOwnership = _out554;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_IndexRange) {
          DAST._IExpression _2280_on = _source109.dtor_expr;
          bool _2281_isArray = _source109.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2282_low = _source109.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2283_high = _source109.dtor_high;
          unmatched109 = false;
          {
            RAST._IExpr _2284_onExpr;
            DCOMP._IOwnership _2285_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2286_recIdents;
            RAST._IExpr _out555;
            DCOMP._IOwnership _out556;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
            (this).GenExpr(_2280_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out555, out _out556, out _out557);
            _2284_onExpr = _out555;
            _2285_onOwned = _out556;
            _2286_recIdents = _out557;
            readIdents = _2286_recIdents;
            Dafny.ISequence<Dafny.Rune> _2287_methodName;
            _2287_methodName = (((_2282_low).is_Some) ? ((((_2283_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2283_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2288_arguments;
            _2288_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source112 = _2282_low;
            bool unmatched112 = true;
            if (unmatched112) {
              if (_source112.is_Some) {
                DAST._IExpression _2289_l = _source112.dtor_value;
                unmatched112 = false;
                {
                  RAST._IExpr _2290_lExpr;
                  DCOMP._IOwnership _2291___v200;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2292_recIdentsL;
                  RAST._IExpr _out558;
                  DCOMP._IOwnership _out559;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
                  (this).GenExpr(_2289_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out558, out _out559, out _out560);
                  _2290_lExpr = _out558;
                  _2291___v200 = _out559;
                  _2292_recIdentsL = _out560;
                  _2288_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2288_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2290_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2292_recIdentsL);
                }
              }
            }
            if (unmatched112) {
              unmatched112 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source113 = _2283_high;
            bool unmatched113 = true;
            if (unmatched113) {
              if (_source113.is_Some) {
                DAST._IExpression _2293_h = _source113.dtor_value;
                unmatched113 = false;
                {
                  RAST._IExpr _2294_hExpr;
                  DCOMP._IOwnership _2295___v201;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2296_recIdentsH;
                  RAST._IExpr _out561;
                  DCOMP._IOwnership _out562;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
                  (this).GenExpr(_2293_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out561, out _out562, out _out563);
                  _2294_hExpr = _out561;
                  _2295___v201 = _out562;
                  _2296_recIdentsH = _out563;
                  _2288_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2288_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2294_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2296_recIdentsH);
                }
              }
            }
            if (unmatched113) {
              unmatched113 = false;
            }
            r = _2284_onExpr;
            if (_2281_isArray) {
              if (!(_2287_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2287_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2287_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).FSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2287_methodName))).Apply(_2288_arguments);
            } else {
              if (!(_2287_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2287_methodName)).Apply(_2288_arguments);
              }
            }
            RAST._IExpr _out564;
            DCOMP._IOwnership _out565;
            (this).FromOwned(r, expectedOwnership, out _out564, out _out565);
            r = _out564;
            resultingOwnership = _out565;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_TupleSelect) {
          DAST._IExpression _2297_on = _source109.dtor_expr;
          BigInteger _2298_idx = _source109.dtor_index;
          DAST._IType _2299_fieldType = _source109.dtor_fieldType;
          unmatched109 = false;
          {
            RAST._IExpr _2300_onExpr;
            DCOMP._IOwnership _2301_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2302_recIdents;
            RAST._IExpr _out566;
            DCOMP._IOwnership _out567;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
            (this).GenExpr(_2297_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out566, out _out567, out _out568);
            _2300_onExpr = _out566;
            _2301_onOwnership = _out567;
            _2302_recIdents = _out568;
            Dafny.ISequence<Dafny.Rune> _2303_selName;
            _2303_selName = Std.Strings.__default.OfNat(_2298_idx);
            DAST._IType _source114 = _2299_fieldType;
            bool unmatched114 = true;
            if (unmatched114) {
              if (_source114.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2304_tps = _source114.dtor_Tuple_a0;
                unmatched114 = false;
                if (((_2299_fieldType).is_Tuple) && ((new BigInteger((_2304_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2303_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2303_selName);
                }
              }
            }
            if (unmatched114) {
              unmatched114 = false;
            }
            r = ((_2300_onExpr).Sel(_2303_selName)).Clone();
            RAST._IExpr _out569;
            DCOMP._IOwnership _out570;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out569, out _out570);
            r = _out569;
            resultingOwnership = _out570;
            readIdents = _2302_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Call) {
          DAST._IExpression _2305_on = _source109.dtor_on;
          DAST._ICallName _2306_name = _source109.dtor_callName;
          Dafny.ISequence<DAST._IType> _2307_typeArgs = _source109.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2308_args = _source109.dtor_args;
          unmatched109 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2309_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2310_recIdents;
            Dafny.ISequence<RAST._IType> _2311_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2312_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out571;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out572;
            Dafny.ISequence<RAST._IType> _out573;
            Std.Wrappers._IOption<DAST._IResolvedType> _out574;
            (this).GenArgs(selfIdent, _2306_name, _2307_typeArgs, _2308_args, env, out _out571, out _out572, out _out573, out _out574);
            _2309_argExprs = _out571;
            _2310_recIdents = _out572;
            _2311_typeExprs = _out573;
            _2312_fullNameQualifier = _out574;
            readIdents = _2310_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source115 = _2312_fullNameQualifier;
            bool unmatched115 = true;
            if (unmatched115) {
              if (_source115.is_Some) {
                DAST._IResolvedType value11 = _source115.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2313_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2314_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2315_base = value11.dtor_kind;
                unmatched115 = false;
                RAST._IExpr _2316_fullPath;
                RAST._IExpr _out575;
                _out575 = DCOMP.COMP.GenPathExpr(_2313_path, true);
                _2316_fullPath = _out575;
                Dafny.ISequence<RAST._IType> _2317_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out576;
                _out576 = (this).GenTypeArgs(_2314_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2317_onTypeExprs = _out576;
                RAST._IExpr _2318_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2319_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2320_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2315_base).is_Trait) || ((_2315_base).is_Class)) {
                  RAST._IExpr _out577;
                  DCOMP._IOwnership _out578;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out579;
                  (this).GenExpr(_2305_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out577, out _out578, out _out579);
                  _2318_onExpr = _out577;
                  _2319_recOwnership = _out578;
                  _2320_recIdents = _out579;
                  _2318_onExpr = ((this).read__macro).Apply1(_2318_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2320_recIdents);
                } else {
                  RAST._IExpr _out580;
                  DCOMP._IOwnership _out581;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out582;
                  (this).GenExpr(_2305_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out580, out _out581, out _out582);
                  _2318_onExpr = _out580;
                  _2319_recOwnership = _out581;
                  _2320_recIdents = _out582;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2320_recIdents);
                }
                r = ((((_2316_fullPath).ApplyType(_2317_onTypeExprs)).FSel(DCOMP.__default.escapeName((_2306_name).dtor_name))).ApplyType(_2311_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2318_onExpr), _2309_argExprs));
                RAST._IExpr _out583;
                DCOMP._IOwnership _out584;
                (this).FromOwned(r, expectedOwnership, out _out583, out _out584);
                r = _out583;
                resultingOwnership = _out584;
              }
            }
            if (unmatched115) {
              unmatched115 = false;
              RAST._IExpr _2321_onExpr;
              DCOMP._IOwnership _2322___v207;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2323_recIdents;
              RAST._IExpr _out585;
              DCOMP._IOwnership _out586;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out587;
              (this).GenExpr(_2305_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out585, out _out586, out _out587);
              _2321_onExpr = _out585;
              _2322___v207 = _out586;
              _2323_recIdents = _out587;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2323_recIdents);
              Dafny.ISequence<Dafny.Rune> _2324_renderedName;
              _2324_renderedName = (this).GetMethodName(_2305_on, _2306_name);
              DAST._IExpression _source116 = _2305_on;
              bool unmatched116 = true;
              if (unmatched116) {
                bool disjunctiveMatch17 = false;
                if (_source116.is_Companion) {
                  disjunctiveMatch17 = true;
                }
                if (_source116.is_ExternCompanion) {
                  disjunctiveMatch17 = true;
                }
                if (disjunctiveMatch17) {
                  unmatched116 = false;
                  {
                    _2321_onExpr = (_2321_onExpr).FSel(_2324_renderedName);
                  }
                }
              }
              if (unmatched116) {
                unmatched116 = false;
                {
                  if (!object.Equals(_2321_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source117 = _2306_name;
                    bool unmatched117 = true;
                    if (unmatched117) {
                      if (_source117.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source117.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2325_tpe = onType2.dtor_value;
                          unmatched117 = false;
                          RAST._IType _2326_typ;
                          RAST._IType _out588;
                          _out588 = (this).GenType(_2325_tpe, DCOMP.GenTypeContext.@default());
                          _2326_typ = _out588;
                          if ((_2326_typ).IsObjectOrPointer()) {
                            _2321_onExpr = ((this).read__macro).Apply1(_2321_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched117) {
                      unmatched117 = false;
                    }
                  }
                  _2321_onExpr = (_2321_onExpr).Sel(_2324_renderedName);
                }
              }
              r = ((_2321_onExpr).ApplyType(_2311_typeExprs)).Apply(_2309_argExprs);
              RAST._IExpr _out589;
              DCOMP._IOwnership _out590;
              (this).FromOwned(r, expectedOwnership, out _out589, out _out590);
              r = _out589;
              resultingOwnership = _out590;
              return ;
            }
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2327_paramsDafny = _source109.dtor_params;
          DAST._IType _2328_retType = _source109.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2329_body = _source109.dtor_body;
          unmatched109 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2330_params;
            Dafny.ISequence<RAST._IFormal> _out591;
            _out591 = (this).GenParams(_2327_paramsDafny, true);
            _2330_params = _out591;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2331_paramNames;
            _2331_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2332_paramTypesMap;
            _2332_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi50 = new BigInteger((_2330_params).Count);
            for (BigInteger _2333_i = BigInteger.Zero; _2333_i < _hi50; _2333_i++) {
              Dafny.ISequence<Dafny.Rune> _2334_name;
              _2334_name = ((_2330_params).Select(_2333_i)).dtor_name;
              _2331_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2331_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2334_name));
              _2332_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2332_paramTypesMap, _2334_name, ((_2330_params).Select(_2333_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2335_subEnv;
            _2335_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2331_paramNames, _2332_paramTypesMap));
            RAST._IExpr _2336_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2337_recIdents;
            DCOMP._IEnvironment _2338___v217;
            RAST._IExpr _out592;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out593;
            DCOMP._IEnvironment _out594;
            (this).GenStmts(_2329_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2335_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out592, out _out593, out _out594);
            _2336_recursiveGen = _out592;
            _2337_recIdents = _out593;
            _2338___v217 = _out594;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2337_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2337_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2339_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll9 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_10 in (_2339_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2340_name = (Dafny.ISequence<Dafny.Rune>)_compr_10;
                if ((_2339_paramNames).Contains(_2340_name)) {
                  _coll9.Add(_2340_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll9);
            }))())(_2331_paramNames));
            RAST._IExpr _2341_allReadCloned;
            _2341_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2337_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2342_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_4 in (_2337_recIdents).Elements) {
                _2342_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_4;
                if ((_2337_recIdents).Contains(_2342_next)) {
                  goto after__ASSIGN_SUCH_THAT_4;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 5230)");
            after__ASSIGN_SUCH_THAT_4: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2342_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2343_selfCloned;
                DCOMP._IOwnership _2344___v218;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2345___v219;
                RAST._IExpr _out595;
                DCOMP._IOwnership _out596;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out597;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out595, out _out596, out _out597);
                _2343_selfCloned = _out595;
                _2344___v218 = _out596;
                _2345___v219 = _out597;
                _2341_allReadCloned = (_2341_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2343_selfCloned)));
              } else if (!((_2331_paramNames).Contains(_2342_next))) {
                RAST._IExpr _2346_copy;
                _2346_copy = (RAST.Expr.create_Identifier(_2342_next)).Clone();
                _2341_allReadCloned = (_2341_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2342_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2346_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2342_next));
              }
              _2337_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2337_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2342_next));
            }
            RAST._IType _2347_retTypeGen;
            RAST._IType _out598;
            _out598 = (this).GenType(_2328_retType, DCOMP.GenTypeContext.InFn());
            _2347_retTypeGen = _out598;
            r = RAST.Expr.create_Block((_2341_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2330_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2347_retTypeGen), RAST.Expr.create_Block(_2336_recursiveGen)))));
            RAST._IExpr _out599;
            DCOMP._IOwnership _out600;
            (this).FromOwned(r, expectedOwnership, out _out599, out _out600);
            r = _out599;
            resultingOwnership = _out600;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2348_values = _source109.dtor_values;
          DAST._IType _2349_retType = _source109.dtor_retType;
          DAST._IExpression _2350_expr = _source109.dtor_expr;
          unmatched109 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2351_paramNames;
            _2351_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2352_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out601;
            _out601 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2353_value) => {
              return (_2353_value).dtor__0;
            })), _2348_values), false);
            _2352_paramFormals = _out601;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2354_paramTypes;
            _2354_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2355_paramNamesSet;
            _2355_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi51 = new BigInteger((_2348_values).Count);
            for (BigInteger _2356_i = BigInteger.Zero; _2356_i < _hi51; _2356_i++) {
              Dafny.ISequence<Dafny.Rune> _2357_name;
              _2357_name = (((_2348_values).Select(_2356_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2358_rName;
              _2358_rName = DCOMP.__default.escapeVar(_2357_name);
              _2351_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2351_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2358_rName));
              _2354_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2354_paramTypes, _2358_rName, ((_2352_paramFormals).Select(_2356_i)).dtor_tpe);
              _2355_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2355_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2358_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi52 = new BigInteger((_2348_values).Count);
            for (BigInteger _2359_i = BigInteger.Zero; _2359_i < _hi52; _2359_i++) {
              RAST._IType _2360_typeGen;
              RAST._IType _out602;
              _out602 = (this).GenType((((_2348_values).Select(_2359_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2360_typeGen = _out602;
              RAST._IExpr _2361_valueGen;
              DCOMP._IOwnership _2362___v220;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2363_recIdents;
              RAST._IExpr _out603;
              DCOMP._IOwnership _out604;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out605;
              (this).GenExpr(((_2348_values).Select(_2359_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out603, out _out604, out _out605);
              _2361_valueGen = _out603;
              _2362___v220 = _out604;
              _2363_recIdents = _out605;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar((((_2348_values).Select(_2359_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2360_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2361_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2363_recIdents);
            }
            DCOMP._IEnvironment _2364_newEnv;
            _2364_newEnv = DCOMP.Environment.create(_2351_paramNames, _2354_paramTypes);
            RAST._IExpr _2365_recGen;
            DCOMP._IOwnership _2366_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2367_recIdents;
            RAST._IExpr _out606;
            DCOMP._IOwnership _out607;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out608;
            (this).GenExpr(_2350_expr, selfIdent, _2364_newEnv, expectedOwnership, out _out606, out _out607, out _out608);
            _2365_recGen = _out606;
            _2366_recOwned = _out607;
            _2367_recIdents = _out608;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2367_recIdents, _2355_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2365_recGen));
            RAST._IExpr _out609;
            DCOMP._IOwnership _out610;
            (this).FromOwnership(r, _2366_recOwned, expectedOwnership, out _out609, out _out610);
            r = _out609;
            resultingOwnership = _out610;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2368_name = _source109.dtor_ident;
          DAST._IType _2369_tpe = _source109.dtor_typ;
          DAST._IExpression _2370_value = _source109.dtor_value;
          DAST._IExpression _2371_iifeBody = _source109.dtor_iifeBody;
          unmatched109 = false;
          {
            RAST._IExpr _2372_valueGen;
            DCOMP._IOwnership _2373___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2374_recIdents;
            RAST._IExpr _out611;
            DCOMP._IOwnership _out612;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out613;
            (this).GenExpr(_2370_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out611, out _out612, out _out613);
            _2372_valueGen = _out611;
            _2373___v221 = _out612;
            _2374_recIdents = _out613;
            readIdents = _2374_recIdents;
            RAST._IType _2375_valueTypeGen;
            RAST._IType _out614;
            _out614 = (this).GenType(_2369_tpe, DCOMP.GenTypeContext.InFn());
            _2375_valueTypeGen = _out614;
            RAST._IExpr _2376_bodyGen;
            DCOMP._IOwnership _2377___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2378_bodyIdents;
            RAST._IExpr _out615;
            DCOMP._IOwnership _out616;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out617;
            (this).GenExpr(_2371_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out615, out _out616, out _out617);
            _2376_bodyGen = _out615;
            _2377___v222 = _out616;
            _2378_bodyIdents = _out617;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2378_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_2368_name))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar(_2368_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2375_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2372_valueGen))).Then(_2376_bodyGen));
            RAST._IExpr _out618;
            DCOMP._IOwnership _out619;
            (this).FromOwned(r, expectedOwnership, out _out618, out _out619);
            r = _out618;
            resultingOwnership = _out619;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Apply) {
          DAST._IExpression _2379_func = _source109.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2380_args = _source109.dtor_args;
          unmatched109 = false;
          {
            RAST._IExpr _2381_funcExpr;
            DCOMP._IOwnership _2382___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2383_recIdents;
            RAST._IExpr _out620;
            DCOMP._IOwnership _out621;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
            (this).GenExpr(_2379_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out620, out _out621, out _out622);
            _2381_funcExpr = _out620;
            _2382___v223 = _out621;
            _2383_recIdents = _out622;
            readIdents = _2383_recIdents;
            Dafny.ISequence<RAST._IExpr> _2384_rArgs;
            _2384_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi53 = new BigInteger((_2380_args).Count);
            for (BigInteger _2385_i = BigInteger.Zero; _2385_i < _hi53; _2385_i++) {
              RAST._IExpr _2386_argExpr;
              DCOMP._IOwnership _2387_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2388_argIdents;
              RAST._IExpr _out623;
              DCOMP._IOwnership _out624;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out625;
              (this).GenExpr((_2380_args).Select(_2385_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out623, out _out624, out _out625);
              _2386_argExpr = _out623;
              _2387_argOwned = _out624;
              _2388_argIdents = _out625;
              _2384_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2384_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2386_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2388_argIdents);
            }
            r = (_2381_funcExpr).Apply(_2384_rArgs);
            RAST._IExpr _out626;
            DCOMP._IOwnership _out627;
            (this).FromOwned(r, expectedOwnership, out _out626, out _out627);
            r = _out626;
            resultingOwnership = _out627;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_TypeTest) {
          DAST._IExpression _2389_on = _source109.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2390_dType = _source109.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2391_variant = _source109.dtor_variant;
          unmatched109 = false;
          {
            RAST._IExpr _2392_exprGen;
            DCOMP._IOwnership _2393___v224;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2394_recIdents;
            RAST._IExpr _out628;
            DCOMP._IOwnership _out629;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out630;
            (this).GenExpr(_2389_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out628, out _out629, out _out630);
            _2392_exprGen = _out628;
            _2393___v224 = _out629;
            _2394_recIdents = _out630;
            RAST._IType _2395_dTypePath;
            RAST._IType _out631;
            _out631 = DCOMP.COMP.GenPathType(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2390_dType, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2391_variant)));
            _2395_dTypePath = _out631;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2392_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_2395_dTypePath)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out632;
            DCOMP._IOwnership _out633;
            (this).FromOwned(r, expectedOwnership, out _out632, out _out633);
            r = _out632;
            resultingOwnership = _out633;
            readIdents = _2394_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Is) {
          DAST._IExpression _2396_expr = _source109.dtor_expr;
          DAST._IType _2397_fromType = _source109.dtor_fromType;
          DAST._IType _2398_toType = _source109.dtor_toType;
          unmatched109 = false;
          {
            RAST._IExpr _2399_expr;
            DCOMP._IOwnership _2400_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2401_recIdents;
            RAST._IExpr _out634;
            DCOMP._IOwnership _out635;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out636;
            (this).GenExpr(_2396_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out634, out _out635, out _out636);
            _2399_expr = _out634;
            _2400_recOwned = _out635;
            _2401_recIdents = _out636;
            RAST._IType _2402_fromType;
            RAST._IType _out637;
            _out637 = (this).GenType(_2397_fromType, DCOMP.GenTypeContext.@default());
            _2402_fromType = _out637;
            RAST._IType _2403_toType;
            RAST._IType _out638;
            _out638 = (this).GenType(_2398_toType, DCOMP.GenTypeContext.@default());
            _2403_toType = _out638;
            if (((_2402_fromType).IsObject()) && ((_2403_toType).IsObject())) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is_instance_of_object"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((_2402_fromType).ObjectOrPointerUnderlying(), (_2403_toType).ObjectOrPointerUnderlying()))).Apply1(_2399_expr);
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Source and/or target types of type test is/are not Object"));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
            RAST._IExpr _out639;
            DCOMP._IOwnership _out640;
            (this).FromOwnership(r, _2400_recOwned, expectedOwnership, out _out639, out _out640);
            r = _out639;
            resultingOwnership = _out640;
            readIdents = _2401_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_BoolBoundedPool) {
          unmatched109 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out641;
            DCOMP._IOwnership _out642;
            (this).FromOwned(r, expectedOwnership, out _out641, out _out642);
            r = _out641;
            resultingOwnership = _out642;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SetBoundedPool) {
          DAST._IExpression _2404_of = _source109.dtor_of;
          unmatched109 = false;
          {
            RAST._IExpr _2405_exprGen;
            DCOMP._IOwnership _2406___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2407_recIdents;
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out645;
            (this).GenExpr(_2404_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out643, out _out644, out _out645);
            _2405_exprGen = _out643;
            _2406___v225 = _out644;
            _2407_recIdents = _out645;
            r = ((_2405_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out646;
            DCOMP._IOwnership _out647;
            (this).FromOwned(r, expectedOwnership, out _out646, out _out647);
            r = _out646;
            resultingOwnership = _out647;
            readIdents = _2407_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SeqBoundedPool) {
          DAST._IExpression _2408_of = _source109.dtor_of;
          bool _2409_includeDuplicates = _source109.dtor_includeDuplicates;
          unmatched109 = false;
          {
            RAST._IExpr _2410_exprGen;
            DCOMP._IOwnership _2411___v226;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2412_recIdents;
            RAST._IExpr _out648;
            DCOMP._IOwnership _out649;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out650;
            (this).GenExpr(_2408_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out648, out _out649, out _out650);
            _2410_exprGen = _out648;
            _2411___v226 = _out649;
            _2412_recIdents = _out650;
            r = ((_2410_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2409_includeDuplicates)) {
              r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).AsExpr()).Apply1(r);
            }
            RAST._IExpr _out651;
            DCOMP._IOwnership _out652;
            (this).FromOwned(r, expectedOwnership, out _out651, out _out652);
            r = _out651;
            resultingOwnership = _out652;
            readIdents = _2412_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapBoundedPool) {
          DAST._IExpression _2413_of = _source109.dtor_of;
          unmatched109 = false;
          {
            RAST._IExpr _2414_exprGen;
            DCOMP._IOwnership _2415___v227;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2416_recIdents;
            RAST._IExpr _out653;
            DCOMP._IOwnership _out654;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
            (this).GenExpr(_2413_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out653, out _out654, out _out655);
            _2414_exprGen = _out653;
            _2415___v227 = _out654;
            _2416_recIdents = _out655;
            r = ((((_2414_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2416_recIdents;
            RAST._IExpr _out656;
            DCOMP._IOwnership _out657;
            (this).FromOwned(r, expectedOwnership, out _out656, out _out657);
            r = _out656;
            resultingOwnership = _out657;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_IntRange) {
          DAST._IExpression _2417_lo = _source109.dtor_lo;
          DAST._IExpression _2418_hi = _source109.dtor_hi;
          bool _2419_up = _source109.dtor_up;
          unmatched109 = false;
          {
            RAST._IExpr _2420_lo;
            DCOMP._IOwnership _2421___v228;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2422_recIdentsLo;
            RAST._IExpr _out658;
            DCOMP._IOwnership _out659;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out660;
            (this).GenExpr(_2417_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out658, out _out659, out _out660);
            _2420_lo = _out658;
            _2421___v228 = _out659;
            _2422_recIdentsLo = _out660;
            RAST._IExpr _2423_hi;
            DCOMP._IOwnership _2424___v229;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2425_recIdentsHi;
            RAST._IExpr _out661;
            DCOMP._IOwnership _out662;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out663;
            (this).GenExpr(_2418_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out661, out _out662, out _out663);
            _2423_hi = _out661;
            _2424___v229 = _out662;
            _2425_recIdentsHi = _out663;
            if (_2419_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2420_lo, _2423_hi));
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2423_hi, _2420_lo));
            }
            RAST._IExpr _out664;
            DCOMP._IOwnership _out665;
            (this).FromOwned(r, expectedOwnership, out _out664, out _out665);
            r = _out664;
            resultingOwnership = _out665;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2422_recIdentsLo, _2425_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_UnboundedIntRange) {
          DAST._IExpression _2426_start = _source109.dtor_start;
          bool _2427_up = _source109.dtor_up;
          unmatched109 = false;
          {
            RAST._IExpr _2428_start;
            DCOMP._IOwnership _2429___v230;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2430_recIdentStart;
            RAST._IExpr _out666;
            DCOMP._IOwnership _out667;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out668;
            (this).GenExpr(_2426_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out666, out _out667, out _out668);
            _2428_start = _out666;
            _2429___v230 = _out667;
            _2430_recIdentStart = _out668;
            if (_2427_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).AsExpr()).Apply1(_2428_start);
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).AsExpr()).Apply1(_2428_start);
            }
            RAST._IExpr _out669;
            DCOMP._IOwnership _out670;
            (this).FromOwned(r, expectedOwnership, out _out669, out _out670);
            r = _out669;
            resultingOwnership = _out670;
            readIdents = _2430_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapBuilder) {
          DAST._IType _2431_keyType = _source109.dtor_keyType;
          DAST._IType _2432_valueType = _source109.dtor_valueType;
          unmatched109 = false;
          {
            RAST._IType _2433_kType;
            RAST._IType _out671;
            _out671 = (this).GenType(_2431_keyType, DCOMP.GenTypeContext.@default());
            _2433_kType = _out671;
            RAST._IType _2434_vType;
            RAST._IType _out672;
            _out672 = (this).GenType(_2432_valueType, DCOMP.GenTypeContext.@default());
            _2434_vType = _out672;
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2433_kType, _2434_vType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out673;
            DCOMP._IOwnership _out674;
            (this).FromOwned(r, expectedOwnership, out _out673, out _out674);
            r = _out673;
            resultingOwnership = _out674;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SetBuilder) {
          DAST._IType _2435_elemType = _source109.dtor_elemType;
          unmatched109 = false;
          {
            RAST._IType _2436_eType;
            RAST._IType _out675;
            _out675 = (this).GenType(_2435_elemType, DCOMP.GenTypeContext.@default());
            _2436_eType = _out675;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2436_eType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out676;
            DCOMP._IOwnership _out677;
            (this).FromOwned(r, expectedOwnership, out _out676, out _out677);
            r = _out676;
            resultingOwnership = _out677;
            return ;
          }
        }
      }
      if (unmatched109) {
        DAST._IType _2437_elemType = _source109.dtor_elemType;
        DAST._IExpression _2438_collection = _source109.dtor_collection;
        bool _2439_is__forall = _source109.dtor_is__forall;
        DAST._IExpression _2440_lambda = _source109.dtor_lambda;
        unmatched109 = false;
        {
          RAST._IType _2441_tpe;
          RAST._IType _out678;
          _out678 = (this).GenType(_2437_elemType, DCOMP.GenTypeContext.@default());
          _2441_tpe = _out678;
          RAST._IExpr _2442_collectionGen;
          DCOMP._IOwnership _2443___v231;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2444_recIdents;
          RAST._IExpr _out679;
          DCOMP._IOwnership _out680;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out681;
          (this).GenExpr(_2438_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out679, out _out680, out _out681);
          _2442_collectionGen = _out679;
          _2443___v231 = _out680;
          _2444_recIdents = _out681;
          Dafny.ISequence<DAST._IAttribute> _2445_extraAttributes;
          _2445_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2438_collection).is_IntRange) || ((_2438_collection).is_UnboundedIntRange)) || ((_2438_collection).is_SeqBoundedPool)) {
            _2445_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2440_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2446_formals;
            _2446_formals = (_2440_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2447_newFormals;
            _2447_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi54 = new BigInteger((_2446_formals).Count);
            for (BigInteger _2448_i = BigInteger.Zero; _2448_i < _hi54; _2448_i++) {
              var _pat_let_tv201 = _2445_extraAttributes;
              var _pat_let_tv202 = _2446_formals;
              _2447_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2447_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2446_formals).Select(_2448_i), _pat_let49_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let49_0, _2449_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv201, ((_pat_let_tv202).Select(_2448_i)).dtor_attributes), _pat_let50_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let50_0, _2450_dt__update_hattributes_h0 => DAST.Formal.create((_2449_dt__update__tmp_h0).dtor_name, (_2449_dt__update__tmp_h0).dtor_typ, _2450_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv203 = _2447_newFormals;
            DAST._IExpression _2451_newLambda;
            _2451_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2440_lambda, _pat_let51_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let51_0, _2452_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv203, _pat_let52_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let52_0, _2453_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2453_dt__update_hparams_h0, (_2452_dt__update__tmp_h1).dtor_retType, (_2452_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2454_lambdaGen;
            DCOMP._IOwnership _2455___v232;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2456_recLambdaIdents;
            RAST._IExpr _out682;
            DCOMP._IOwnership _out683;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out684;
            (this).GenExpr(_2451_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out682, out _out683, out _out684);
            _2454_lambdaGen = _out682;
            _2455___v232 = _out683;
            _2456_recLambdaIdents = _out684;
            Dafny.ISequence<Dafny.Rune> _2457_fn;
            _2457_fn = ((_2439_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2442_collectionGen).Sel(_2457_fn)).Apply1(((_2454_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2444_recIdents, _2456_recLambdaIdents);
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Quantifier without an inline lambda"));
            r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
          RAST._IExpr _out685;
          DCOMP._IOwnership _out686;
          (this).FromOwned(r, expectedOwnership, out _out685, out _out686);
          r = _out685;
          resultingOwnership = _out686;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> externalFiles)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      Dafny.ISequence<RAST._IModDecl> _2458_externUseDecls;
      _2458_externUseDecls = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi55 = new BigInteger((externalFiles).Count);
      for (BigInteger _2459_i = BigInteger.Zero; _2459_i < _hi55; _2459_i++) {
        Dafny.ISequence<Dafny.Rune> _2460_externalFile;
        _2460_externalFile = (externalFiles).Select(_2459_i);
        Dafny.ISequence<Dafny.Rune> _2461_externalMod;
        _2461_externalMod = _2460_externalFile;
        if (((new BigInteger((_2460_externalFile).Count)) > (new BigInteger(3))) && (((_2460_externalFile).Drop((new BigInteger((_2460_externalFile).Count)) - (new BigInteger(3)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".rs")))) {
          _2461_externalMod = (_2460_externalFile).Subsequence(BigInteger.Zero, (new BigInteger((_2460_externalFile).Count)) - (new BigInteger(3)));
        } else {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unrecognized external file "), _2460_externalFile), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". External file must be *.rs files")));
        }
        RAST._IMod _2462_externMod;
        _2462_externMod = RAST.Mod.create_ExternMod(_2461_externalMod);
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (_2462_externMod)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        _2458_externUseDecls = Dafny.Sequence<RAST._IModDecl>.Concat(_2458_externUseDecls, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), ((RAST.__default.crate).MSel(_2461_externalMod)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))));
      }
      if (!(_2458_externUseDecls).Equals(Dafny.Sequence<RAST._IModDecl>.FromElements())) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (RAST.Mod.create_Mod(DCOMP.COMP.DAFNY__EXTERN__MODULE, _2458_externUseDecls))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
      }
      DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _2463_allModules;
      _2463_allModules = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Empty();
      BigInteger _hi56 = new BigInteger((p).Count);
      for (BigInteger _2464_i = BigInteger.Zero; _2464_i < _hi56; _2464_i++) {
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _2465_m;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out687;
        _out687 = (this).GenModule((p).Select(_2464_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2465_m = _out687;
        _2463_allModules = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(_2463_allModules, _2465_m);
      }
      BigInteger _hi57 = new BigInteger(((_2463_allModules).dtor_keys).Count);
      for (BigInteger _2466_i = BigInteger.Zero; _2466_i < _hi57; _2466_i++) {
        if (!((_2463_allModules).dtor_values).Contains(((_2463_allModules).dtor_keys).Select(_2466_i))) {
          goto continue_0;
        }
        RAST._IMod _2467_m;
        _2467_m = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Select((_2463_allModules).dtor_values,((_2463_allModules).dtor_keys).Select(_2466_i))).ToRust();
        BigInteger _hi58 = new BigInteger((this.optimizations).Count);
        for (BigInteger _2468_j = BigInteger.Zero; _2468_j < _hi58; _2468_j++) {
          _2467_m = Dafny.Helpers.Id<Func<RAST._IMod, RAST._IMod>>((this.optimizations).Select(_2468_j))(_2467_m);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (_2467_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      continue_0: ;
      }
    after_0: ;
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2469_i;
      _2469_i = BigInteger.Zero;
      while ((_2469_i) < (new BigInteger((fullName).Count))) {
        if ((_2469_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2469_i)));
        _2469_i = (_2469_i) + (BigInteger.One);
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
      return ((RAST.__default.dafny__runtime).MSel(((((this).ObjectType).is_RawPointers) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("modify!")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("md!"))))).AsExpr();
    } }
    public RAST._IExpr read__macro { get {
      return ((RAST.__default.dafny__runtime).MSel(((((this).ObjectType).is_RawPointers) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read!")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rd!"))))).AsExpr();
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