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
      Dafny.ISequence<Dafny.Rune> _1291___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1291___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1291___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1291___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in137 = (i).Drop(new BigInteger(2));
        i = _in137;
        goto TAIL_CALL_START;
      } else {
        _1291___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1291___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in138 = (i).Drop(BigInteger.One);
        i = _in138;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1292___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1292___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1292___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1292___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in139 = (i).Drop(BigInteger.One);
        i = _in139;
        goto TAIL_CALL_START;
      } else {
        _1292___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1292___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1293_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1293_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeVar(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1294_r = (f);
      if ((DCOMP.__default.reserved__vars).Contains(_1294_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1294_r);
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
      var _pat_let_tv188 = dafnyName;
      var _pat_let_tv189 = rs;
      var _pat_let_tv190 = dafnyName;
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _1295_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source65 = (rs).Select(BigInteger.Zero);
          bool unmatched65 = true;
          if (unmatched65) {
            if (_source65.is_UserDefined) {
              DAST._IResolvedType _1296_resolvedType = _source65.dtor_resolved;
              unmatched65 = false;
              return DCOMP.__default.TraitTypeContainingMethod(_1296_resolvedType, _pat_let_tv188);
            }
          }
          if (unmatched65) {
            unmatched65 = false;
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
          throw new System.Exception("unexpected control point");
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source66 = _1295_res;
        bool unmatched66 = true;
        if (unmatched66) {
          if (_source66.is_Some) {
            unmatched66 = false;
            return _1295_res;
          }
        }
        if (unmatched66) {
          unmatched66 = false;
          return DCOMP.__default.TraitTypeContainingMethodAux((_pat_let_tv189).Drop(BigInteger.One), _pat_let_tv190);
        }
        throw new System.Exception("unexpected control point");
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethod(DAST._IResolvedType r, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DAST._IResolvedType _let_tmp_rhs53 = r;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1297_path = _let_tmp_rhs53.dtor_path;
      Dafny.ISequence<DAST._IType> _1298_typeArgs = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedTypeBase _1299_kind = _let_tmp_rhs53.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1300_attributes = _let_tmp_rhs53.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1301_properMethods = _let_tmp_rhs53.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1302_extendedTypes = _let_tmp_rhs53.dtor_extendedTypes;
      if ((_1301_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1302_extendedTypes, dafnyName);
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
      Dafny.ISequence<Dafny.Rune> _1303___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1303___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((s).Select(BigInteger.Zero)) == (new Dafny.Rune(' '))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1303___accumulator, s);
      } else {
        _1303___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1303___accumulator, ((((s).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")) : (Dafny.Sequence<Dafny.Rune>.FromElements((s).Select(BigInteger.Zero)))));
        Dafny.ISequence<Dafny.Rune> _in141 = (s).Drop(BigInteger.One);
        s = _in141;
        goto TAIL_CALL_START;
      }
    }
    public static DCOMP._IExternAttribute ExtractExtern(Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DCOMP._IExternAttribute res = DCOMP.ExternAttribute.Default();
      BigInteger _hi5 = new BigInteger((attributes).Count);
      for (BigInteger _1304_i = BigInteger.Zero; _1304_i < _hi5; _1304_i++) {
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _1305_attr;
        _1305_attr = DCOMP.__default.OptExtern((attributes).Select(_1304_i), dafnyName);
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _source67 = _1305_attr;
        bool unmatched67 = true;
        if (unmatched67) {
          if (_source67.is_Some) {
            DCOMP._IExternAttribute _1306_n = _source67.dtor_value;
            unmatched67 = false;
            res = _1306_n;
            return res;
          }
        }
        if (unmatched67) {
          unmatched67 = false;
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
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"));
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
      DCOMP._IEnvironment _1307_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1308_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll8 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_9 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1309_k = (Dafny.ISequence<Dafny.Rune>)_compr_9;
          if (((this).dtor_types).Contains(_1309_k)) {
            _coll8.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_1309_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_1309_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll8);
      }))();
      return DCOMP.Environment.create((_1307_dt__update__tmp_h0).dtor_names, _1308_dt__update_htypes_h0);
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
      BigInteger _1310_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1310_indexInEnv), ((this).dtor_names).Drop((_1310_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      var oth = other as DCOMP.GenTypeContext;
      return oth != null && this._forTraitParents == oth._forTraitParents;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._forTraitParents));
      return (int) hash;
    }
    public override string ToString() {
      string s = "DafnyToRustCompiler.GenTypeContext.GenTypeContext";
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
        return RAST.__default.PtrType(underlying);
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
    }
    public static Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> ContainingPathToRust(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath) {
      return Std.Collections.Seq.__default.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1311_i) => {
        return DCOMP.__default.escapeName((_1311_i));
      })), containingPath);
    }
    public bool HasTestAttribute(Dafny.ISequence<DAST._IAttribute> attributes) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1312_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1312_attributes).UniqueElements, false, (((_exists_var_2) => {
        DAST._IAttribute _1313_attribute = (DAST._IAttribute)_exists_var_2;
        return ((_1312_attributes).Contains(_1313_attribute)) && ((((_1313_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("test"))) && ((new BigInteger(((_1313_attribute).dtor_args).Count)).Sign == 0));
      }))))(attributes);
    }
    public DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> s = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Default();
      _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs54 = DafnyCompilerRustUtils.__default.DafnyNameToContainingPathAndName((mod).dtor_name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1314_innerPath = _let_tmp_rhs54.dtor__0;
      Dafny.ISequence<Dafny.Rune> _1315_innerName = _let_tmp_rhs54.dtor__1;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1316_containingPath;
      _1316_containingPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, _1314_innerPath);
      Dafny.ISequence<Dafny.Rune> _1317_modName;
      _1317_modName = DCOMP.__default.escapeName(_1315_innerName);
      if (((mod).dtor_body).is_None) {
        s = DafnyCompilerRustUtils.GatheringModule.Wrap(DCOMP.COMP.ContainingPathToRust(_1316_containingPath), RAST.Mod.create_ExternMod(_1317_modName));
      } else {
        DCOMP._IExternAttribute _1318_optExtern;
        _1318_optExtern = DCOMP.__default.ExtractExternMod(mod);
        Dafny.ISequence<RAST._IModDecl> _1319_body;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _1320_allmodules;
        Dafny.ISequence<RAST._IModDecl> _out15;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out16;
        (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1316_containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1315_innerName)), out _out15, out _out16);
        _1319_body = _out15;
        _1320_allmodules = _out16;
        if ((_1318_optExtern).is_SimpleExtern) {
          if ((mod).dtor_requiresExterns) {
            _1319_body = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (((RAST.__default.crate).MSel(DCOMP.COMP.DAFNY__EXTERN__MODULE)).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1318_optExtern).dtor_overrideName))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))), _1319_body);
          }
        } else if ((_1318_optExtern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Externs on modules can only have 1 string argument"));
        } else if ((_1318_optExtern).is_UnsupportedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some((_1318_optExtern).dtor_reason);
        }
        Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1321_attributes;
        _1321_attributes = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
        if ((this).HasTestAttribute((mod).dtor_attributes)) {
          _1321_attributes = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[cfg(test)]"));
        }
        s = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(DafnyCompilerRustUtils.GatheringModule.Wrap(DCOMP.COMP.ContainingPathToRust(_1316_containingPath), RAST.Mod.create_Mod(_1317_modName, _1321_attributes, _1319_body)), _1320_allmodules);
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
      for (BigInteger _1322_i = BigInteger.Zero; _1322_i < _hi6; _1322_i++) {
        Dafny.ISequence<RAST._IModDecl> _1323_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source68 = (body).Select(_1322_i);
        bool unmatched68 = true;
        if (unmatched68) {
          if (_source68.is_Module) {
            DAST._IModule _1324_m = _source68.dtor_Module_a0;
            unmatched68 = false;
            DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _1325_mm;
            DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out17;
            _out17 = (this).GenModule(_1324_m, containingPath);
            _1325_mm = _out17;
            allmodules = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(allmodules, _1325_mm);
            _1323_generated = Dafny.Sequence<RAST._IModDecl>.FromElements();
          }
        }
        if (unmatched68) {
          if (_source68.is_Class) {
            DAST._IClass _1326_c = _source68.dtor_Class_a0;
            unmatched68 = false;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenClass(_1326_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1326_c).dtor_name)));
            _1323_generated = _out18;
          }
        }
        if (unmatched68) {
          if (_source68.is_Trait) {
            DAST._ITrait _1327_t = _source68.dtor_Trait_a0;
            unmatched68 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenTrait(_1327_t, containingPath);
            _1323_generated = _out19;
          }
        }
        if (unmatched68) {
          if (_source68.is_Newtype) {
            DAST._INewtype _1328_n = _source68.dtor_Newtype_a0;
            unmatched68 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenNewtype(_1328_n);
            _1323_generated = _out20;
          }
        }
        if (unmatched68) {
          if (_source68.is_SynonymType) {
            DAST._ISynonymType _1329_s = _source68.dtor_SynonymType_a0;
            unmatched68 = false;
            Dafny.ISequence<RAST._IModDecl> _out21;
            _out21 = (this).GenSynonymType(_1329_s);
            _1323_generated = _out21;
          }
        }
        if (unmatched68) {
          DAST._IDatatype _1330_d = _source68.dtor_Datatype_a0;
          unmatched68 = false;
          Dafny.ISequence<RAST._IModDecl> _out22;
          _out22 = (this).GenDatatype(_1330_d);
          _1323_generated = _out22;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1323_generated);
      }
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1331_genTpConstraint;
      _1331_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1331_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1331_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1331_genTpConstraint);
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
        for (BigInteger _1332_tpI = BigInteger.Zero; _1332_tpI < _hi7; _1332_tpI++) {
          DAST._ITypeArgDecl _1333_tp;
          _1333_tp = (@params).Select(_1332_tpI);
          DAST._IType _1334_typeArg;
          RAST._ITypeParamDecl _1335_typeParam;
          DAST._IType _out23;
          RAST._ITypeParamDecl _out24;
          (this).GenTypeParam(_1333_tp, out _out23, out _out24);
          _1334_typeArg = _out23;
          _1335_typeParam = _out24;
          RAST._IType _1336_rType;
          RAST._IType _out25;
          _out25 = (this).GenType(_1334_typeArg, DCOMP.GenTypeContext.@default());
          _1336_rType = _out25;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1334_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1336_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1335_typeParam));
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
    public Dafny.ISet<Dafny.ISequence<Dafny.Rune>> GatherTypeParamNames(Dafny.ISet<Dafny.ISequence<Dafny.Rune>> types, RAST._IType typ)
    {
      return (typ).Fold<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>(types, ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>, RAST._IType, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)((_1337_types, _1338_currentType) => {
        return (((_1338_currentType).is_TIdentifier) ? (Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1337_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_1338_currentType).dtor_name))) : (_1337_types));
      })));
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1339_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1340_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1341_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1342_whereConstraints;
      Dafny.ISequence<DAST._IType> _out26;
      Dafny.ISequence<RAST._IType> _out27;
      Dafny.ISequence<RAST._ITypeParamDecl> _out28;
      Dafny.ISequence<Dafny.Rune> _out29;
      (this).GenTypeParameters((c).dtor_typeParams, out _out26, out _out27, out _out28, out _out29);
      _1339_typeParamsSeq = _out26;
      _1340_rTypeParams = _out27;
      _1341_rTypeParamsDecls = _out28;
      _1342_whereConstraints = _out29;
      Dafny.ISequence<Dafny.Rune> _1343_constrainedTypeParams;
      _1343_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1341_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1344_fields;
      _1344_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1345_fieldInits;
      _1345_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1346_usedTypeParams;
      _1346_usedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi8 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1347_fieldI = BigInteger.Zero; _1347_fieldI < _hi8; _1347_fieldI++) {
        DAST._IField _1348_field;
        _1348_field = ((c).dtor_fields).Select(_1347_fieldI);
        RAST._IType _1349_fieldType;
        RAST._IType _out30;
        _out30 = (this).GenType(((_1348_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1349_fieldType = _out30;
        _1346_usedTypeParams = (this).GatherTypeParamNames(_1346_usedTypeParams, _1349_fieldType);
        Dafny.ISequence<Dafny.Rune> _1350_fieldRustName;
        _1350_fieldRustName = DCOMP.__default.escapeVar(((_1348_field).dtor_formal).dtor_name);
        _1344_fields = Dafny.Sequence<RAST._IField>.Concat(_1344_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1350_fieldRustName, _1349_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source69 = (_1348_field).dtor_defaultValue;
        bool unmatched69 = true;
        if (unmatched69) {
          if (_source69.is_Some) {
            DAST._IExpression _1351_e = _source69.dtor_value;
            unmatched69 = false;
            {
              RAST._IExpr _1352_expr;
              DCOMP._IOwnership _1353___v51;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1354___v52;
              RAST._IExpr _out31;
              DCOMP._IOwnership _out32;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out33;
              (this).GenExpr(_1351_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out31, out _out32, out _out33);
              _1352_expr = _out31;
              _1353___v51 = _out32;
              _1354___v52 = _out33;
              _1345_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1345_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1350_fieldRustName, _1352_expr)));
            }
          }
        }
        if (unmatched69) {
          unmatched69 = false;
          {
            RAST._IExpr _1355_default;
            _1355_default = RAST.__default.std__Default__default;
            if ((_1349_fieldType).IsObjectOrPointer()) {
              _1355_default = (_1349_fieldType).ToNullExpr();
            }
            _1345_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1345_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1350_fieldRustName, _1355_default)));
          }
        }
      }
      BigInteger _hi9 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1356_typeParamI = BigInteger.Zero; _1356_typeParamI < _hi9; _1356_typeParamI++) {
        DAST._IType _1357_typeArg;
        RAST._ITypeParamDecl _1358_typeParam;
        DAST._IType _out34;
        RAST._ITypeParamDecl _out35;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1356_typeParamI), out _out34, out _out35);
        _1357_typeArg = _out34;
        _1358_typeParam = _out35;
        RAST._IType _1359_rTypeArg;
        RAST._IType _out36;
        _out36 = (this).GenType(_1357_typeArg, DCOMP.GenTypeContext.@default());
        _1359_rTypeArg = _out36;
        if ((_1346_usedTypeParams).Contains((_1358_typeParam).dtor_name)) {
          goto continue_0;
        }
        _1344_fields = Dafny.Sequence<RAST._IField>.Concat(_1344_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1356_typeParamI)), RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1359_rTypeArg))))));
        _1345_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1345_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1356_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      continue_0: ;
      }
    after_0: ;
      DCOMP._IExternAttribute _1360_extern;
      _1360_extern = DCOMP.__default.ExtractExtern((c).dtor_attributes, (c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _1361_className = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((_1360_extern).is_SimpleExtern) {
        _1361_className = (_1360_extern).dtor_overrideName;
      } else {
        _1361_className = DCOMP.__default.escapeName((c).dtor_name);
        if ((_1360_extern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multi-argument externs not supported for classes yet"));
        }
      }
      RAST._IStruct _1362_struct;
      _1362_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1361_className, _1341_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1344_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_1360_extern).is_NoExtern) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1362_struct)));
      }
      Dafny.ISequence<RAST._IImplMember> _1363_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1364_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out37;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out38;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1339_typeParamsSeq, out _out37, out _out38);
      _1363_implBody = _out37;
      _1364_traitBodies = _out38;
      if (((_1360_extern).is_NoExtern) && (!(_1361_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default")))) {
        _1363_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.__default.SelfOwned)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel((this).allocate)).AsExpr()).ApplyType1(RAST.__default.SelfOwned)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1363_implBody);
      }
      RAST._IType _1365_selfTypeForImpl = RAST.Type.Default();
      if (((_1360_extern).is_NoExtern) || ((_1360_extern).is_UnsupportedExtern)) {
        _1365_selfTypeForImpl = RAST.Type.create_TIdentifier(_1361_className);
      } else if ((_1360_extern).is_AdvancedExtern) {
        _1365_selfTypeForImpl = (((RAST.__default.crate).MSel((_1360_extern).dtor_enclosingModule)).MSel((_1360_extern).dtor_overrideName)).AsType();
      } else if ((_1360_extern).is_SimpleExtern) {
        _1365_selfTypeForImpl = RAST.Type.create_TIdentifier((_1360_extern).dtor_overrideName);
      }
      if ((new BigInteger((_1363_implBody).Count)).Sign == 1) {
        RAST._IImpl _1366_i;
        _1366_i = RAST.Impl.create_Impl(_1341_rTypeParamsDecls, RAST.Type.create_TypeApp(_1365_selfTypeForImpl, _1340_rTypeParams), _1342_whereConstraints, _1363_implBody);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1366_i)));
      }
      Dafny.ISequence<RAST._IModDecl> _1367_testMethods;
      _1367_testMethods = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_1361_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        BigInteger _hi10 = new BigInteger(((c).dtor_body).Count);
        for (BigInteger _1368_i = BigInteger.Zero; _1368_i < _hi10; _1368_i++) {
          DAST._IMethod _1369_m;
          _1369_m = ((System.Func<DAST._IMethod>)(() => {
            DAST._IMethod _source70 = ((c).dtor_body).Select(_1368_i);
            bool unmatched70 = true;
            if (unmatched70) {
              DAST._IMethod _1370_m = _source70;
              unmatched70 = false;
              return _1370_m;
            }
            throw new System.Exception("unexpected control point");
          }))();
          if (((this).HasTestAttribute((_1369_m).dtor_attributes)) && ((new BigInteger(((_1369_m).dtor_params).Count)).Sign == 0)) {
            Dafny.ISequence<Dafny.Rune> _1371_fnName;
            _1371_fnName = DCOMP.__default.escapeName((_1369_m).dtor_name);
            _1367_testMethods = Dafny.Sequence<RAST._IModDecl>.Concat(_1367_testMethods, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[test]")), RAST.Visibility.create_PUB(), RAST.Fn.create(_1371_fnName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))).FSel(_1371_fnName)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())))))));
          }
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1367_testMethods);
      }
      RAST._IType _1372_genSelfPath;
      RAST._IType _out39;
      _out39 = DCOMP.COMP.GenPathType(path);
      _1372_genSelfPath = _out39;
      if (!(_1361_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1341_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(RAST.__default.AnyTrait))), RAST.Type.create_TypeApp(_1372_genSelfPath, _1340_rTypeParams), _1342_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(RAST.__default.AnyTrait)))))))));
      }
      Dafny.ISequence<DAST._IType> _1373_superClasses;
      _1373_superClasses = (((_1361_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) ? (Dafny.Sequence<DAST._IType>.FromElements()) : ((c).dtor_superClasses));
      BigInteger _hi11 = new BigInteger((_1373_superClasses).Count);
      for (BigInteger _1374_i = BigInteger.Zero; _1374_i < _hi11; _1374_i++) {
        DAST._IType _1375_superClass;
        _1375_superClass = (_1373_superClasses).Select(_1374_i);
        DAST._IType _source71 = _1375_superClass;
        bool unmatched71 = true;
        if (unmatched71) {
          if (_source71.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source71.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1376_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1377_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1378_properMethods = resolved0.dtor_properMethods;
              unmatched71 = false;
              {
                RAST._IType _1379_pathStr;
                RAST._IType _out40;
                _out40 = DCOMP.COMP.GenPathType(_1376_traitPath);
                _1379_pathStr = _out40;
                Dafny.ISequence<RAST._IType> _1380_typeArgs;
                Dafny.ISequence<RAST._IType> _out41;
                _out41 = (this).GenTypeArgs(_1377_typeArgs, DCOMP.GenTypeContext.@default());
                _1380_typeArgs = _out41;
                Dafny.ISequence<RAST._IImplMember> _1381_body;
                _1381_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1364_traitBodies).Contains(_1376_traitPath)) {
                  _1381_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1364_traitBodies,_1376_traitPath);
                }
                RAST._IType _1382_traitType;
                _1382_traitType = RAST.Type.create_TypeApp(_1379_pathStr, _1380_typeArgs);
                if (!((_1360_extern).is_NoExtern)) {
                  if (((new BigInteger((_1381_body).Count)).Sign == 0) && ((new BigInteger((_1378_properMethods).Count)).Sign != 0)) {
                    goto continue_1;
                  }
                  if ((new BigInteger((_1381_body).Count)) != (new BigInteger((_1378_properMethods).Count))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: In the class "), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(path, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1383_s) => {
  return ((_1383_s));
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", some proper methods of ")), (_1382_traitType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" are marked {:extern} and some are not.")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" For the Rust compiler, please make all methods (")), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_1378_properMethods, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1384_s) => {
  return (_1384_s);
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")  bodiless and mark as {:extern} and implement them in a Rust file, ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("or mark none of them as {:extern} and implement them in Dafny. ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.")));
                  }
                }
                RAST._IModDecl _1385_x;
                _1385_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1341_rTypeParamsDecls, _1382_traitType, RAST.Type.create_TypeApp(_1372_genSelfPath, _1340_rTypeParams), _1342_whereConstraints, _1381_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1385_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1341_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1382_traitType))), RAST.Type.create_TypeApp(_1372_genSelfPath, _1340_rTypeParams), _1342_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1382_traitType)))))))));
              }
            }
          }
        }
        if (unmatched71) {
          unmatched71 = false;
        }
      continue_1: ;
      }
    after_1: ;
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1386_typeParamsSeq;
      _1386_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1387_typeParamDecls;
      _1387_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1388_typeParams;
      _1388_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi12 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1389_tpI = BigInteger.Zero; _1389_tpI < _hi12; _1389_tpI++) {
          DAST._ITypeArgDecl _1390_tp;
          _1390_tp = ((t).dtor_typeParams).Select(_1389_tpI);
          DAST._IType _1391_typeArg;
          RAST._ITypeParamDecl _1392_typeParamDecl;
          DAST._IType _out42;
          RAST._ITypeParamDecl _out43;
          (this).GenTypeParam(_1390_tp, out _out42, out _out43);
          _1391_typeArg = _out42;
          _1392_typeParamDecl = _out43;
          _1386_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1386_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1391_typeArg));
          _1387_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1387_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1392_typeParamDecl));
          RAST._IType _1393_typeParam;
          RAST._IType _out44;
          _out44 = (this).GenType(_1391_typeArg, DCOMP.GenTypeContext.@default());
          _1393_typeParam = _out44;
          _1388_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1388_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1393_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1394_fullPath;
      _1394_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1395_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1396___v56;
      Dafny.ISequence<RAST._IImplMember> _out45;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out46;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1394_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1386_typeParamsSeq, out _out45, out _out46);
      _1395_implBody = _out45;
      _1396___v56 = _out46;
      Dafny.ISequence<RAST._IType> _1397_parents;
      _1397_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi13 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1398_i = BigInteger.Zero; _1398_i < _hi13; _1398_i++) {
        RAST._IType _1399_tpe;
        RAST._IType _out47;
        _out47 = (this).GenType(((t).dtor_parents).Select(_1398_i), DCOMP.GenTypeContext.ForTraitParents());
        _1399_tpe = _out47;
        _1397_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1397_parents, Dafny.Sequence<RAST._IType>.FromElements(_1399_tpe)), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply1(RAST.Type.create_DynType(_1399_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1387_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1388_typeParams), _1397_parents, _1395_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1400_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1401_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1402_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1403_whereConstraints;
      Dafny.ISequence<DAST._IType> _out48;
      Dafny.ISequence<RAST._IType> _out49;
      Dafny.ISequence<RAST._ITypeParamDecl> _out50;
      Dafny.ISequence<Dafny.Rune> _out51;
      (this).GenTypeParameters((c).dtor_typeParams, out _out48, out _out49, out _out50, out _out51);
      _1400_typeParamsSeq = _out48;
      _1401_rTypeParams = _out49;
      _1402_rTypeParamsDecls = _out50;
      _1403_whereConstraints = _out51;
      Dafny.ISequence<Dafny.Rune> _1404_constrainedTypeParams;
      _1404_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1402_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1405_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source72 = DCOMP.COMP.NewtypeRangeToRustType((c).dtor_range);
      bool unmatched72 = true;
      if (unmatched72) {
        if (_source72.is_Some) {
          RAST._IType _1406_v = _source72.dtor_value;
          unmatched72 = false;
          _1405_underlyingType = _1406_v;
        }
      }
      if (unmatched72) {
        unmatched72 = false;
        RAST._IType _out52;
        _out52 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1405_underlyingType = _out52;
      }
      DAST._IType _1407_resultingType;
      _1407_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1408_newtypeName;
      _1408_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1408_newtypeName, _1402_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1405_underlyingType))))));
      RAST._IExpr _1409_fnBody;
      _1409_fnBody = RAST.Expr.create_Identifier(_1408_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source73 = (c).dtor_witnessExpr;
      bool unmatched73 = true;
      if (unmatched73) {
        if (_source73.is_Some) {
          DAST._IExpression _1410_e = _source73.dtor_value;
          unmatched73 = false;
          {
            DAST._IExpression _1411_e;
            _1411_e = ((object.Equals((c).dtor_base, _1407_resultingType)) ? (_1410_e) : (DAST.Expression.create_Convert(_1410_e, (c).dtor_base, _1407_resultingType)));
            RAST._IExpr _1412_eStr;
            DCOMP._IOwnership _1413___v57;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1414___v58;
            RAST._IExpr _out53;
            DCOMP._IOwnership _out54;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out55;
            (this).GenExpr(_1411_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out53, out _out54, out _out55);
            _1412_eStr = _out53;
            _1413___v57 = _out54;
            _1414___v58 = _out55;
            _1409_fnBody = (_1409_fnBody).Apply1(_1412_eStr);
          }
        }
      }
      if (unmatched73) {
        unmatched73 = false;
        {
          _1409_fnBody = (_1409_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1415_body;
      _1415_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1409_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source74 = (c).dtor_constraint;
      bool unmatched74 = true;
      if (unmatched74) {
        if (_source74.is_None) {
          unmatched74 = false;
        }
      }
      if (unmatched74) {
        DAST._INewtypeConstraint value8 = _source74.dtor_value;
        DAST._IFormal _1416_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1417_constraintStmts = value8.dtor_constraintStmts;
        unmatched74 = false;
        RAST._IExpr _1418_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1419___v59;
        DCOMP._IEnvironment _1420_newEnv;
        RAST._IExpr _out56;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out57;
        DCOMP._IEnvironment _out58;
        (this).GenStmts(_1417_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out56, out _out57, out _out58);
        _1418_rStmts = _out56;
        _1419___v59 = _out57;
        _1420_newEnv = _out58;
        Dafny.ISequence<RAST._IFormal> _1421_rFormals;
        Dafny.ISequence<RAST._IFormal> _out59;
        _out59 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1416_formal), false);
        _1421_rFormals = _out59;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1402_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1408_newtypeName), _1401_rTypeParams), _1403_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1421_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1418_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1402_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1408_newtypeName), _1401_rTypeParams), _1403_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1415_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1402_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1408_newtypeName), _1401_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1402_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1408_newtypeName), _1401_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1405_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(((RAST.Path.create_Self()).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))).AsType())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1422_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1423_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1424_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1425_whereConstraints;
      Dafny.ISequence<DAST._IType> _out60;
      Dafny.ISequence<RAST._IType> _out61;
      Dafny.ISequence<RAST._ITypeParamDecl> _out62;
      Dafny.ISequence<Dafny.Rune> _out63;
      (this).GenTypeParameters((c).dtor_typeParams, out _out60, out _out61, out _out62, out _out63);
      _1422_typeParamsSeq = _out60;
      _1423_rTypeParams = _out61;
      _1424_rTypeParamsDecls = _out62;
      _1425_whereConstraints = _out63;
      Dafny.ISequence<Dafny.Rune> _1426_synonymTypeName;
      _1426_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1427_resultingType;
      RAST._IType _out64;
      _out64 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1427_resultingType = _out64;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1426_synonymTypeName, _1424_rTypeParamsDecls, _1427_resultingType)));
      Dafny.ISequence<RAST._ITypeParamDecl> _1428_defaultConstrainedTypeParams;
      _1428_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1424_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Std.Wrappers._IOption<DAST._IExpression> _source75 = (c).dtor_witnessExpr;
      bool unmatched75 = true;
      if (unmatched75) {
        if (_source75.is_Some) {
          DAST._IExpression _1429_e = _source75.dtor_value;
          unmatched75 = false;
          {
            RAST._IExpr _1430_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1431___v60;
            DCOMP._IEnvironment _1432_newEnv;
            RAST._IExpr _out65;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out66;
            DCOMP._IEnvironment _out67;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out65, out _out66, out _out67);
            _1430_rStmts = _out65;
            _1431___v60 = _out66;
            _1432_newEnv = _out67;
            RAST._IExpr _1433_rExpr;
            DCOMP._IOwnership _1434___v61;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1435___v62;
            RAST._IExpr _out68;
            DCOMP._IOwnership _out69;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out70;
            (this).GenExpr(_1429_e, DCOMP.SelfInfo.create_NoSelf(), _1432_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out68, out _out69, out _out70);
            _1433_rExpr = _out68;
            _1434___v61 = _out69;
            _1435___v62 = _out70;
            Dafny.ISequence<Dafny.Rune> _1436_constantName;
            _1436_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1436_constantName, _1428_defaultConstrainedTypeParams, Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1427_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1430_rStmts).Then(_1433_rExpr)))))));
          }
        }
      }
      if (unmatched75) {
        unmatched75 = false;
      }
      return s;
    }
    public bool TypeIsEq(DAST._IType t) {
      DAST._IType _source76 = t;
      bool unmatched76 = true;
      if (unmatched76) {
        if (_source76.is_UserDefined) {
          unmatched76 = false;
          return true;
        }
      }
      if (unmatched76) {
        if (_source76.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1437_ts = _source76.dtor_Tuple_a0;
          unmatched76 = false;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1438_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1438_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1439_t = (DAST._IType)_forall_var_5;
            return !((_1438_ts).Contains(_1439_t)) || ((this).TypeIsEq(_1439_t));
          }))))(_1437_ts);
        }
      }
      if (unmatched76) {
        if (_source76.is_Array) {
          DAST._IType _1440_t = _source76.dtor_element;
          unmatched76 = false;
          return (this).TypeIsEq(_1440_t);
        }
      }
      if (unmatched76) {
        if (_source76.is_Seq) {
          DAST._IType _1441_t = _source76.dtor_element;
          unmatched76 = false;
          return (this).TypeIsEq(_1441_t);
        }
      }
      if (unmatched76) {
        if (_source76.is_Set) {
          DAST._IType _1442_t = _source76.dtor_element;
          unmatched76 = false;
          return (this).TypeIsEq(_1442_t);
        }
      }
      if (unmatched76) {
        if (_source76.is_Multiset) {
          DAST._IType _1443_t = _source76.dtor_element;
          unmatched76 = false;
          return (this).TypeIsEq(_1443_t);
        }
      }
      if (unmatched76) {
        if (_source76.is_Map) {
          DAST._IType _1444_k = _source76.dtor_key;
          DAST._IType _1445_v = _source76.dtor_value;
          unmatched76 = false;
          return ((this).TypeIsEq(_1444_k)) && ((this).TypeIsEq(_1445_v));
        }
      }
      if (unmatched76) {
        if (_source76.is_SetBuilder) {
          DAST._IType _1446_t = _source76.dtor_element;
          unmatched76 = false;
          return (this).TypeIsEq(_1446_t);
        }
      }
      if (unmatched76) {
        if (_source76.is_MapBuilder) {
          DAST._IType _1447_k = _source76.dtor_key;
          DAST._IType _1448_v = _source76.dtor_value;
          unmatched76 = false;
          return ((this).TypeIsEq(_1447_k)) && ((this).TypeIsEq(_1448_v));
        }
      }
      if (unmatched76) {
        if (_source76.is_Arrow) {
          unmatched76 = false;
          return false;
        }
      }
      if (unmatched76) {
        if (_source76.is_Primitive) {
          unmatched76 = false;
          return true;
        }
      }
      if (unmatched76) {
        if (_source76.is_Passthrough) {
          unmatched76 = false;
          return true;
        }
      }
      if (unmatched76) {
        if (_source76.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _1449_i = _source76.dtor_TypeArg_a0;
          unmatched76 = false;
          return true;
        }
      }
      if (unmatched76) {
        unmatched76 = false;
        return true;
      }
      throw new System.Exception("unexpected control point");
    }
    public bool DatatypeIsEq(DAST._IDatatype c) {
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1450_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1450_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1451_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1451_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1452_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1450_c).dtor_ctors).Contains(_1451_ctor)) && (((_1451_ctor).dtor_args).Contains(_1452_arg))) || ((this).TypeIsEq(((_1452_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1453_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1454_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1455_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1456_whereConstraints;
      Dafny.ISequence<DAST._IType> _out71;
      Dafny.ISequence<RAST._IType> _out72;
      Dafny.ISequence<RAST._ITypeParamDecl> _out73;
      Dafny.ISequence<Dafny.Rune> _out74;
      (this).GenTypeParameters((c).dtor_typeParams, out _out71, out _out72, out _out73, out _out74);
      _1453_typeParamsSeq = _out71;
      _1454_rTypeParams = _out72;
      _1455_rTypeParamsDecls = _out73;
      _1456_whereConstraints = _out74;
      Dafny.ISequence<Dafny.Rune> _1457_datatypeName;
      _1457_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1458_ctors;
      _1458_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _1459_variances;
      _1459_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_1460_typeParamDecl) => {
        return (_1460_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1461_usedTypeParams;
      _1461_usedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.ISequence<RAST._IExpr> _1462_singletonConstructors;
      _1462_singletonConstructors = Dafny.Sequence<RAST._IExpr>.FromElements();
      BigInteger _hi14 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1463_i = BigInteger.Zero; _1463_i < _hi14; _1463_i++) {
        DAST._IDatatypeCtor _1464_ctor;
        _1464_ctor = ((c).dtor_ctors).Select(_1463_i);
        Dafny.ISequence<RAST._IField> _1465_ctorArgs;
        _1465_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1466_isNumeric;
        _1466_isNumeric = false;
        if ((new BigInteger(((_1464_ctor).dtor_args).Count)).Sign == 0) {
          RAST._IExpr _1467_instantiation;
          _1467_instantiation = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1457_datatypeName)).FSel(DCOMP.__default.escapeName((_1464_ctor).dtor_name)), Dafny.Sequence<RAST._IAssignIdentifier>.FromElements());
          if ((this).IsRcWrapped((c).dtor_attributes)) {
            _1467_instantiation = RAST.__default.RcNew(_1467_instantiation);
          }
          _1462_singletonConstructors = Dafny.Sequence<RAST._IExpr>.Concat(_1462_singletonConstructors, Dafny.Sequence<RAST._IExpr>.FromElements(_1467_instantiation));
        }
        BigInteger _hi15 = new BigInteger(((_1464_ctor).dtor_args).Count);
        for (BigInteger _1468_j = BigInteger.Zero; _1468_j < _hi15; _1468_j++) {
          DAST._IDatatypeDtor _1469_dtor;
          _1469_dtor = ((_1464_ctor).dtor_args).Select(_1468_j);
          RAST._IType _1470_formalType;
          RAST._IType _out75;
          _out75 = (this).GenType(((_1469_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1470_formalType = _out75;
          _1461_usedTypeParams = (this).GatherTypeParamNames(_1461_usedTypeParams, _1470_formalType);
          Dafny.ISequence<Dafny.Rune> _1471_formalName;
          _1471_formalName = DCOMP.__default.escapeVar(((_1469_dtor).dtor_formal).dtor_name);
          if (((_1468_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1471_formalName))) {
            _1466_isNumeric = true;
          }
          if ((((_1468_j).Sign != 0) && (_1466_isNumeric)) && (!(Std.Strings.__default.OfNat(_1468_j)).Equals(_1471_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1471_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1468_j)));
            _1466_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1465_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1465_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1471_formalName, RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1470_formalType))))));
          } else {
            _1465_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1465_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1471_formalName, _1470_formalType))));
          }
        }
        RAST._IFields _1472_namedFields;
        _1472_namedFields = RAST.Fields.create_NamedFields(_1465_ctorArgs);
        if (_1466_isNumeric) {
          _1472_namedFields = (_1472_namedFields).ToNamelessFields();
        }
        _1458_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1458_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1464_ctor).dtor_name), _1472_namedFields)));
      }
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1473_unusedTypeParams;
      _1473_unusedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Helpers.Id<Func<Dafny.ISequence<RAST._ITypeParamDecl>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_1474_rTypeParamsDecls) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
        var _coll9 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
        foreach (RAST._ITypeParamDecl _compr_10 in (_1474_rTypeParamsDecls).CloneAsArray()) {
          RAST._ITypeParamDecl _1475_tp = (RAST._ITypeParamDecl)_compr_10;
          if ((_1474_rTypeParamsDecls).Contains(_1475_tp)) {
            _coll9.Add((_1475_tp).dtor_name);
          }
        }
        return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll9);
      }))())(_1455_rTypeParamsDecls), _1461_usedTypeParams);
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1476_selfPath;
      _1476_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1477_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1478_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out76;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out77;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1476_selfPath, _1453_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1459_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1453_typeParamsSeq, out _out76, out _out77);
      _1477_implBodyRaw = _out76;
      _1478_traitBodies = _out77;
      Dafny.ISequence<RAST._IImplMember> _1479_implBody;
      _1479_implBody = _1477_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1480_emittedFields;
      _1480_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1481_i = BigInteger.Zero; _1481_i < _hi16; _1481_i++) {
        DAST._IDatatypeCtor _1482_ctor;
        _1482_ctor = ((c).dtor_ctors).Select(_1481_i);
        BigInteger _hi17 = new BigInteger(((_1482_ctor).dtor_args).Count);
        for (BigInteger _1483_j = BigInteger.Zero; _1483_j < _hi17; _1483_j++) {
          DAST._IDatatypeDtor _1484_dtor;
          _1484_dtor = ((_1482_ctor).dtor_args).Select(_1483_j);
          Dafny.ISequence<Dafny.Rune> _1485_callName;
          _1485_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1484_dtor).dtor_callName, DCOMP.__default.escapeVar(((_1484_dtor).dtor_formal).dtor_name));
          if (!((_1480_emittedFields).Contains(_1485_callName))) {
            _1480_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1480_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1485_callName));
            RAST._IType _1486_formalType;
            RAST._IType _out78;
            _out78 = (this).GenType(((_1484_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1486_formalType = _out78;
            Dafny.ISequence<RAST._IMatchCase> _1487_cases;
            _1487_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi18 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1488_k = BigInteger.Zero; _1488_k < _hi18; _1488_k++) {
              DAST._IDatatypeCtor _1489_ctor2;
              _1489_ctor2 = ((c).dtor_ctors).Select(_1488_k);
              Dafny.ISequence<Dafny.Rune> _1490_pattern;
              _1490_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1457_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1489_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1491_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1492_hasMatchingField;
              _1492_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1493_patternInner;
              _1493_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1494_isNumeric;
              _1494_isNumeric = false;
              BigInteger _hi19 = new BigInteger(((_1489_ctor2).dtor_args).Count);
              for (BigInteger _1495_l = BigInteger.Zero; _1495_l < _hi19; _1495_l++) {
                DAST._IDatatypeDtor _1496_dtor2;
                _1496_dtor2 = ((_1489_ctor2).dtor_args).Select(_1495_l);
                Dafny.ISequence<Dafny.Rune> _1497_patternName;
                _1497_patternName = DCOMP.__default.escapeVar(((_1496_dtor2).dtor_formal).dtor_name);
                if (((_1495_l).Sign == 0) && ((_1497_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1494_isNumeric = true;
                }
                if (_1494_isNumeric) {
                  _1497_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1496_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1495_l)));
                }
                if (object.Equals(((_1484_dtor).dtor_formal).dtor_name, ((_1496_dtor2).dtor_formal).dtor_name)) {
                  _1492_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1497_patternName);
                }
                _1493_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1493_patternInner, _1497_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1494_isNumeric) {
                _1490_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1490_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1493_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1490_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1490_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1493_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1492_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1491_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1492_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1491_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1492_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1491_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _1498_ctorMatch;
              _1498_ctorMatch = RAST.MatchCase.create(_1490_pattern, RAST.Expr.create_RawExpr(_1491_rhs));
              _1487_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1487_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1498_ctorMatch));
            }
            if (((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) && ((new BigInteger((_1473_unusedTypeParams).Count)).Sign == 1)) {
              _1487_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1487_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1457_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _1499_methodBody;
            _1499_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1487_cases);
            _1479_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1479_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1485_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1486_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1499_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1500_coerceTypes;
      _1500_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1501_rCoerceTypeParams;
      _1501_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1502_coerceArguments;
      _1502_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1503_coerceMap;
      _1503_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1504_rCoerceMap;
      _1504_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1505_coerceMapToArg;
      _1505_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1506_types;
        _1506_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi20 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1507_typeI = BigInteger.Zero; _1507_typeI < _hi20; _1507_typeI++) {
          DAST._ITypeArgDecl _1508_typeParam;
          _1508_typeParam = ((c).dtor_typeParams).Select(_1507_typeI);
          DAST._IType _1509_typeArg;
          RAST._ITypeParamDecl _1510_rTypeParamDecl;
          DAST._IType _out79;
          RAST._ITypeParamDecl _out80;
          (this).GenTypeParam(_1508_typeParam, out _out79, out _out80);
          _1509_typeArg = _out79;
          _1510_rTypeParamDecl = _out80;
          RAST._IType _1511_rTypeArg;
          RAST._IType _out81;
          _out81 = (this).GenType(_1509_typeArg, DCOMP.GenTypeContext.@default());
          _1511_rTypeArg = _out81;
          _1506_types = Dafny.Sequence<RAST._IType>.Concat(_1506_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1511_rTypeArg))));
          if (((_1507_typeI) < (new BigInteger((_1459_variances).Count))) && (((_1459_variances).Select(_1507_typeI)).is_Nonvariant)) {
            _1500_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1500_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1511_rTypeArg));
            goto continue_2_0;
          }
          DAST._ITypeArgDecl _1512_coerceTypeParam;
          _1512_coerceTypeParam = Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_1508_typeParam, _pat_let20_0 => Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_pat_let20_0, _1513_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1507_typeI)), _pat_let21_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(_pat_let21_0, _1514_dt__update_hname_h0 => DAST.TypeArgDecl.create(_1514_dt__update_hname_h0, (_1513_dt__update__tmp_h0).dtor_bounds, (_1513_dt__update__tmp_h0).dtor_variance)))));
          DAST._IType _1515_coerceTypeArg;
          RAST._ITypeParamDecl _1516_rCoerceTypeParamDecl;
          DAST._IType _out82;
          RAST._ITypeParamDecl _out83;
          (this).GenTypeParam(_1512_coerceTypeParam, out _out82, out _out83);
          _1515_coerceTypeArg = _out82;
          _1516_rCoerceTypeParamDecl = _out83;
          _1503_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1503_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1509_typeArg, _1515_coerceTypeArg)));
          RAST._IType _1517_rCoerceType;
          RAST._IType _out84;
          _out84 = (this).GenType(_1515_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1517_rCoerceType = _out84;
          _1504_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1504_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1511_rTypeArg, _1517_rCoerceType)));
          _1500_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1500_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1517_rCoerceType));
          _1501_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1501_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1516_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1518_coerceFormal;
          _1518_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1507_typeI));
          _1505_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1505_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1511_rTypeArg, _1517_rCoerceType), (RAST.Expr.create_Identifier(_1518_coerceFormal)).Clone())));
          _1502_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1502_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1518_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1511_rTypeArg), _1517_rCoerceType)), RAST.__default.StaticTrait)))));
        continue_2_0: ;
        }
      after_2_0: ;
        if ((new BigInteger((_1473_unusedTypeParams).Count)).Sign == 1) {
          _1458_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1458_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1519_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1519_tpe);
})), _1506_types)))));
        }
      }
      bool _1520_cIsEq;
      _1520_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1520_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1457_datatypeName, _1455_rTypeParamsDecls, _1458_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1455_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1457_datatypeName), _1454_rTypeParams), _1456_whereConstraints, _1479_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1521_printImplBodyCases;
      _1521_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1522_hashImplBodyCases;
      _1522_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1523_coerceImplBodyCases;
      _1523_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi21 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1524_i = BigInteger.Zero; _1524_i < _hi21; _1524_i++) {
        DAST._IDatatypeCtor _1525_ctor;
        _1525_ctor = ((c).dtor_ctors).Select(_1524_i);
        Dafny.ISequence<Dafny.Rune> _1526_ctorMatch;
        _1526_ctorMatch = DCOMP.__default.escapeName((_1525_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1527_modulePrefix;
        _1527_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1528_ctorName;
        _1528_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1527_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1525_ctor).dtor_name));
        if (((new BigInteger((_1528_ctorName).Count)) >= (new BigInteger(13))) && (((_1528_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1528_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1529_printRhs;
        _1529_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1528_ctorName), (((_1525_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1530_hashRhs;
        _1530_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1531_coerceRhsArgs;
        _1531_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1532_isNumeric;
        _1532_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1533_ctorMatchInner;
        _1533_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi22 = new BigInteger(((_1525_ctor).dtor_args).Count);
        for (BigInteger _1534_j = BigInteger.Zero; _1534_j < _hi22; _1534_j++) {
          DAST._IDatatypeDtor _1535_dtor;
          _1535_dtor = ((_1525_ctor).dtor_args).Select(_1534_j);
          Dafny.ISequence<Dafny.Rune> _1536_patternName;
          _1536_patternName = DCOMP.__default.escapeVar(((_1535_dtor).dtor_formal).dtor_name);
          DAST._IType _1537_formalType;
          _1537_formalType = ((_1535_dtor).dtor_formal).dtor_typ;
          if (((_1534_j).Sign == 0) && ((_1536_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1532_isNumeric = true;
          }
          if (_1532_isNumeric) {
            _1536_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1535_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1534_j)));
          }
          _1530_hashRhs = (((_1537_formalType).is_Arrow) ? ((_1530_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))) : ((_1530_hashRhs).Then((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1536_patternName), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state")))))));
          _1533_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1533_ctorMatchInner, _1536_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1534_j).Sign == 1) {
            _1529_printRhs = (_1529_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1529_printRhs = (_1529_printRhs).Then(RAST.Expr.create_RawExpr((((_1537_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1536_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1538_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1539_formalTpe;
          RAST._IType _out85;
          _out85 = (this).GenType(_1537_formalType, DCOMP.GenTypeContext.@default());
          _1539_formalTpe = _out85;
          DAST._IType _1540_newFormalType;
          _1540_newFormalType = (_1537_formalType).Replace(_1503_coerceMap);
          RAST._IType _1541_newFormalTpe;
          _1541_newFormalTpe = (_1539_formalTpe).ReplaceMap(_1504_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1542_upcastConverter;
          _1542_upcastConverter = (this).UpcastConversionLambda(_1537_formalType, _1539_formalTpe, _1540_newFormalType, _1541_newFormalTpe, _1505_coerceMapToArg);
          if ((_1542_upcastConverter).is_Success) {
            RAST._IExpr _1543_coercionFunction;
            _1543_coercionFunction = (_1542_upcastConverter).dtor_value;
            _1538_coerceRhsArg = (_1543_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1536_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1534_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1457_datatypeName));
            _1538_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1531_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1531_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1536_patternName, _1538_coerceRhsArg)));
        }
        RAST._IExpr _1544_coerceRhs;
        _1544_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1457_datatypeName)).FSel(DCOMP.__default.escapeName((_1525_ctor).dtor_name)), _1531_coerceRhsArgs);
        if (_1532_isNumeric) {
          _1526_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1526_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1533_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1526_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1526_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1533_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1525_ctor).dtor_hasAnyArgs) {
          _1529_printRhs = (_1529_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1529_printRhs = (_1529_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1521_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1521_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1457_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1526_ctorMatch), RAST.Expr.create_Block(_1529_printRhs))));
        _1522_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1522_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1457_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1526_ctorMatch), RAST.Expr.create_Block(_1530_hashRhs))));
        _1523_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1523_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1457_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1526_ctorMatch), RAST.Expr.create_Block(_1544_coerceRhs))));
      }
      if (((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) && ((new BigInteger((_1473_unusedTypeParams).Count)).Sign == 1)) {
        Dafny.ISequence<RAST._IMatchCase> _1545_extraCases;
        _1545_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1457_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _1521_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1521_printImplBodyCases, _1545_extraCases);
        _1522_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1522_hashImplBodyCases, _1545_extraCases);
        _1523_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1523_coerceImplBodyCases, _1545_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1546_defaultConstrainedTypeParams;
      _1546_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1455_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1547_rTypeParamsDeclsWithEq;
      _1547_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1455_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1548_rTypeParamsDeclsWithHash;
      _1548_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1455_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1549_printImplBody;
      _1549_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1521_printImplBodyCases);
      RAST._IExpr _1550_hashImplBody;
      _1550_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1522_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1455_rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug"))).AsType(), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1457_datatypeName), _1454_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType()))), Std.Wrappers.Option<RAST._IType>.create_Some((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Result"))).AsType()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1455_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1457_datatypeName), _1454_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType())), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1549_printImplBody))))))));
      if ((new BigInteger((_1501_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1551_coerceImplBody;
        _1551_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1523_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1455_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1457_datatypeName), _1454_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1501_rCoerceTypeParams, _1502_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1457_datatypeName), _1454_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1457_datatypeName), _1500_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.__default.SelfOwned)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1457_datatypeName), _1500_coerceTypes)), _1551_coerceImplBody))))))))));
      }
      if ((new BigInteger((_1462_singletonConstructors).Count)) == (new BigInteger(((c).dtor_ctors).Count))) {
        RAST._IType _1552_datatypeType;
        _1552_datatypeType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1457_datatypeName), _1454_rTypeParams);
        RAST._IType _1553_instantiationType;
        _1553_instantiationType = (((this).IsRcWrapped((c).dtor_attributes)) ? (RAST.__default.Rc(_1552_datatypeType)) : (_1552_datatypeType));
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1455_rTypeParamsDecls, _1552_datatypeType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_AllSingletonConstructors"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SequenceIter"))).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1553_instantiationType))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).AsExpr()).Apply(_1462_singletonConstructors)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())))))))));
      }
      if (_1520_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1547_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1457_datatypeName), _1454_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1548_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1457_datatypeName), _1454_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))).AsType()))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1550_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1554_structName;
        _1554_structName = (RAST.Expr.create_Identifier(_1457_datatypeName)).FSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1555_structAssignments;
        _1555_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi23 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1556_i = BigInteger.Zero; _1556_i < _hi23; _1556_i++) {
          DAST._IDatatypeDtor _1557_dtor;
          _1557_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1556_i);
          _1555_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1555_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(((_1557_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1558_defaultConstrainedTypeParams;
        _1558_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1455_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1559_fullType;
        _1559_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1457_datatypeName), _1454_rTypeParams);
        if (_1520_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1558_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1559_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1559_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1554_structName, _1555_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1455_rTypeParamsDecls, ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).AsType()).Apply1(_1559_fullType), RAST.Type.create_Borrowed(_1559_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        BigInteger _hi24 = new BigInteger((p).Count);
        for (BigInteger _1560_i = BigInteger.Zero; _1560_i < _hi24; _1560_i++) {
          Dafny.ISequence<Dafny.Rune> _1561_name;
          _1561_name = ((p).Select(_1560_i));
          if (escape) {
            _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs55 = DafnyCompilerRustUtils.__default.DafnyNameToContainingPathAndName(_1561_name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1562_modules = _let_tmp_rhs55.dtor__0;
            Dafny.ISequence<Dafny.Rune> _1563_finalName = _let_tmp_rhs55.dtor__1;
            BigInteger _hi25 = new BigInteger((_1562_modules).Count);
            for (BigInteger _1564_j = BigInteger.Zero; _1564_j < _hi25; _1564_j++) {
              r = (r).MSel(DCOMP.__default.escapeName(((_1562_modules).Select(_1564_j))));
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1563_finalName));
          } else {
            r = (r).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1561_name)));
          }
        }
      }
      return r;
    }
    public static RAST._IType GenPathType(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IType t = RAST.Type.Default();
      RAST._IPath _1565_p;
      RAST._IPath _out86;
      _out86 = DCOMP.COMP.GenPath(p, true);
      _1565_p = _out86;
      t = (_1565_p).AsType();
      return t;
    }
    public static RAST._IExpr GenPathExpr(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p, bool escape)
    {
      RAST._IExpr e = RAST.Expr.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        e = RAST.__default.self;
        return e;
      }
      RAST._IPath _1566_p;
      RAST._IPath _out87;
      _out87 = DCOMP.COMP.GenPath(p, escape);
      _1566_p = _out87;
      e = (_1566_p).AsExpr();
      return e;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi26 = new BigInteger((args).Count);
      for (BigInteger _1567_i = BigInteger.Zero; _1567_i < _hi26; _1567_i++) {
        RAST._IType _1568_genTp;
        RAST._IType _out88;
        _out88 = (this).GenType((args).Select(_1567_i), genTypeContext);
        _1568_genTp = _out88;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1568_genTp));
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, bool genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source77 = c;
      bool unmatched77 = true;
      if (unmatched77) {
        if (_source77.is_UserDefined) {
          DAST._IResolvedType _1569_resolved = _source77.dtor_resolved;
          unmatched77 = false;
          {
            RAST._IType _1570_t;
            RAST._IType _out89;
            _out89 = DCOMP.COMP.GenPathType((_1569_resolved).dtor_path);
            _1570_t = _out89;
            Dafny.ISequence<RAST._IType> _1571_typeArgs;
            Dafny.ISequence<RAST._IType> _out90;
            _out90 = (this).GenTypeArgs((_1569_resolved).dtor_typeArgs, false);
            _1571_typeArgs = _out90;
            s = RAST.Type.create_TypeApp(_1570_t, _1571_typeArgs);
            DAST._IResolvedTypeBase _source78 = (_1569_resolved).dtor_kind;
            bool unmatched78 = true;
            if (unmatched78) {
              if (_source78.is_Class) {
                unmatched78 = false;
                {
                  s = (this).Object(s);
                }
              }
            }
            if (unmatched78) {
              if (_source78.is_Datatype) {
                unmatched78 = false;
                {
                  if ((this).IsRcWrapped((_1569_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched78) {
              if (_source78.is_Trait) {
                unmatched78 = false;
                {
                  if (((_1569_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = RAST.__default.AnyTrait;
                  }
                  if (!((genTypeContext))) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched78) {
              DAST._IType _1572_base = _source78.dtor_baseType;
              DAST._INewtypeRange _1573_range = _source78.dtor_range;
              bool _1574_erased = _source78.dtor_erase;
              unmatched78 = false;
              {
                if (_1574_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source79 = DCOMP.COMP.NewtypeRangeToRustType(_1573_range);
                  bool unmatched79 = true;
                  if (unmatched79) {
                    if (_source79.is_Some) {
                      RAST._IType _1575_v = _source79.dtor_value;
                      unmatched79 = false;
                      s = _1575_v;
                    }
                  }
                  if (unmatched79) {
                    unmatched79 = false;
                    RAST._IType _1576_underlying;
                    RAST._IType _out91;
                    _out91 = (this).GenType(_1572_base, DCOMP.GenTypeContext.@default());
                    _1576_underlying = _out91;
                    s = RAST.Type.create_TSynonym(s, _1576_underlying);
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Object) {
          unmatched77 = false;
          {
            s = RAST.__default.AnyTrait;
            if (!((genTypeContext))) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1577_types = _source77.dtor_Tuple_a0;
          unmatched77 = false;
          {
            Dafny.ISequence<RAST._IType> _1578_args;
            _1578_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1579_i;
            _1579_i = BigInteger.Zero;
            while ((_1579_i) < (new BigInteger((_1577_types).Count))) {
              RAST._IType _1580_generated;
              RAST._IType _out92;
              _out92 = (this).GenType((_1577_types).Select(_1579_i), false);
              _1580_generated = _out92;
              _1578_args = Dafny.Sequence<RAST._IType>.Concat(_1578_args, Dafny.Sequence<RAST._IType>.FromElements(_1580_generated));
              _1579_i = (_1579_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1577_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1578_args)) : (RAST.__default.SystemTupleType(_1578_args)));
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Array) {
          DAST._IType _1581_element = _source77.dtor_element;
          BigInteger _1582_dims = _source77.dtor_dims;
          unmatched77 = false;
          {
            if ((_1582_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1583_elem;
              RAST._IType _out93;
              _out93 = (this).GenType(_1581_element, false);
              _1583_elem = _out93;
              if ((_1582_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1583_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1584_n;
                _1584_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1582_dims));
                s = (((RAST.__default.dafny__runtime).MSel(_1584_n)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1583_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Seq) {
          DAST._IType _1585_element = _source77.dtor_element;
          unmatched77 = false;
          {
            RAST._IType _1586_elem;
            RAST._IType _out94;
            _out94 = (this).GenType(_1585_element, false);
            _1586_elem = _out94;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1586_elem));
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Set) {
          DAST._IType _1587_element = _source77.dtor_element;
          unmatched77 = false;
          {
            RAST._IType _1588_elem;
            RAST._IType _out95;
            _out95 = (this).GenType(_1587_element, false);
            _1588_elem = _out95;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1588_elem));
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Multiset) {
          DAST._IType _1589_element = _source77.dtor_element;
          unmatched77 = false;
          {
            RAST._IType _1590_elem;
            RAST._IType _out96;
            _out96 = (this).GenType(_1589_element, false);
            _1590_elem = _out96;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1590_elem));
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Map) {
          DAST._IType _1591_key = _source77.dtor_key;
          DAST._IType _1592_value = _source77.dtor_value;
          unmatched77 = false;
          {
            RAST._IType _1593_keyType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1591_key, false);
            _1593_keyType = _out97;
            RAST._IType _1594_valueType;
            RAST._IType _out98;
            _out98 = (this).GenType(_1592_value, genTypeContext);
            _1594_valueType = _out98;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1593_keyType, _1594_valueType));
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_MapBuilder) {
          DAST._IType _1595_key = _source77.dtor_key;
          DAST._IType _1596_value = _source77.dtor_value;
          unmatched77 = false;
          {
            RAST._IType _1597_keyType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1595_key, false);
            _1597_keyType = _out99;
            RAST._IType _1598_valueType;
            RAST._IType _out100;
            _out100 = (this).GenType(_1596_value, genTypeContext);
            _1598_valueType = _out100;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1597_keyType, _1598_valueType));
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_SetBuilder) {
          DAST._IType _1599_elem = _source77.dtor_element;
          unmatched77 = false;
          {
            RAST._IType _1600_elemType;
            RAST._IType _out101;
            _out101 = (this).GenType(_1599_elem, false);
            _1600_elemType = _out101;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1600_elemType));
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1601_args = _source77.dtor_args;
          DAST._IType _1602_result = _source77.dtor_result;
          unmatched77 = false;
          {
            Dafny.ISequence<RAST._IType> _1603_argTypes;
            _1603_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1604_i;
            _1604_i = BigInteger.Zero;
            while ((_1604_i) < (new BigInteger((_1601_args).Count))) {
              RAST._IType _1605_generated;
              RAST._IType _out102;
              _out102 = (this).GenType((_1601_args).Select(_1604_i), false);
              _1605_generated = _out102;
              _1603_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1603_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1605_generated)));
              _1604_i = (_1604_i) + (BigInteger.One);
            }
            RAST._IType _1606_resultType;
            RAST._IType _out103;
            _out103 = (this).GenType(_1602_result, DCOMP.GenTypeContext.@default());
            _1606_resultType = _out103;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1603_argTypes, _1606_resultType)));
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source77.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1607_name = _h90;
          unmatched77 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1607_name));
        }
      }
      if (unmatched77) {
        if (_source77.is_Primitive) {
          DAST._IPrimitive _1608_p = _source77.dtor_Primitive_a0;
          unmatched77 = false;
          {
            DAST._IPrimitive _source80 = _1608_p;
            bool unmatched80 = true;
            if (unmatched80) {
              if (_source80.is_Int) {
                unmatched80 = false;
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).AsType();
              }
            }
            if (unmatched80) {
              if (_source80.is_Real) {
                unmatched80 = false;
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"))).AsType();
              }
            }
            if (unmatched80) {
              if (_source80.is_String) {
                unmatched80 = false;
                s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType()));
              }
            }
            if (unmatched80) {
              if (_source80.is_Bool) {
                unmatched80 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched80) {
              unmatched80 = false;
              s = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType();
            }
          }
        }
      }
      if (unmatched77) {
        Dafny.ISequence<Dafny.Rune> _1609_v = _source77.dtor_Passthrough_a0;
        unmatched77 = false;
        s = RAST.__default.RawType(_1609_v);
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
      BigInteger _hi27 = new BigInteger((body).Count);
      for (BigInteger _1610_i = BigInteger.Zero; _1610_i < _hi27; _1610_i++) {
        DAST._IMethod _source81 = (body).Select(_1610_i);
        bool unmatched81 = true;
        if (unmatched81) {
          DAST._IMethod _1611_m = _source81;
          unmatched81 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source82 = (_1611_m).dtor_overridingPath;
            bool unmatched82 = true;
            if (unmatched82) {
              if (_source82.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1612_p = _source82.dtor_value;
                unmatched82 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1613_existing;
                  _1613_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1612_p)) {
                    _1613_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1612_p);
                  }
                  if (((new BigInteger(((_1611_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1614_genMethod;
                  RAST._IImplMember _out104;
                  _out104 = (this).GenMethod(_1611_m, true, enclosingType, enclosingTypeParams);
                  _1614_genMethod = _out104;
                  _1613_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1613_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1614_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1612_p, _1613_existing)));
                }
              }
            }
            if (unmatched82) {
              unmatched82 = false;
              {
                RAST._IImplMember _1615_generated;
                RAST._IImplMember _out105;
                _out105 = (this).GenMethod(_1611_m, forTrait, enclosingType, enclosingTypeParams);
                _1615_generated = _out105;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1615_generated));
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
      BigInteger _hi28 = new BigInteger((@params).Count);
      for (BigInteger _1616_i = BigInteger.Zero; _1616_i < _hi28; _1616_i++) {
        DAST._IFormal _1617_param;
        _1617_param = (@params).Select(_1616_i);
        RAST._IType _1618_paramType;
        RAST._IType _out106;
        _out106 = (this).GenType((_1617_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1618_paramType = _out106;
        if (((!((_1618_paramType).CanReadWithoutClone())) || (forLambda)) && (!((_1617_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1618_paramType = RAST.Type.create_Borrowed(_1618_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeVar((_1617_param).dtor_name), _1618_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1619_params;
      Dafny.ISequence<RAST._IFormal> _out107;
      _out107 = (this).GenParams((m).dtor_params, false);
      _1619_params = _out107;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1620_paramNames;
      _1620_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1621_paramTypes;
      _1621_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi29 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1622_paramI = BigInteger.Zero; _1622_paramI < _hi29; _1622_paramI++) {
        DAST._IFormal _1623_dafny__formal;
        _1623_dafny__formal = ((m).dtor_params).Select(_1622_paramI);
        RAST._IFormal _1624_formal;
        _1624_formal = (_1619_params).Select(_1622_paramI);
        Dafny.ISequence<Dafny.Rune> _1625_name;
        _1625_name = (_1624_formal).dtor_name;
        _1620_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1620_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1625_name));
        _1621_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1621_paramTypes, _1625_name, (_1624_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1626_fnName;
      _1626_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1627_selfIdent;
      _1627_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1628_selfId;
        _1628_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1628_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv191 = enclosingTypeParams;
        var _pat_let_tv192 = enclosingType;
        DAST._IType _1629_instanceType;
        _1629_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source83 = enclosingType;
          bool unmatched83 = true;
          if (unmatched83) {
            if (_source83.is_UserDefined) {
              DAST._IResolvedType _1630_r = _source83.dtor_resolved;
              unmatched83 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1630_r, _pat_let22_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let22_0, _1631_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv191, _pat_let23_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let23_0, _1632_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1631_dt__update__tmp_h0).dtor_path, _1632_dt__update_htypeArgs_h0, (_1631_dt__update__tmp_h0).dtor_kind, (_1631_dt__update__tmp_h0).dtor_attributes, (_1631_dt__update__tmp_h0).dtor_properMethods, (_1631_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched83) {
            unmatched83 = false;
            return _pat_let_tv192;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1633_selfFormal;
          _1633_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1619_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1633_selfFormal), _1619_params);
        } else {
          RAST._IType _1634_tpe;
          RAST._IType _out108;
          _out108 = (this).GenType(_1629_instanceType, DCOMP.GenTypeContext.@default());
          _1634_tpe = _out108;
          if ((_1628_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            if (((this).ObjectType).is_RcMut) {
              _1634_tpe = RAST.Type.create_Borrowed(_1634_tpe);
            }
          } else if ((_1628_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1634_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1634_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1634_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _1634_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.__default.SelfOwned));
              } else {
                _1634_tpe = RAST.Type.create_Borrowed(RAST.__default.SelfOwned);
              }
            }
          }
          _1619_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1628_selfId, _1634_tpe)), _1619_params);
        }
        _1627_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1628_selfId, _1629_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1635_retTypeArgs;
      _1635_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1636_typeI;
      _1636_typeI = BigInteger.Zero;
      while ((_1636_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1637_typeExpr;
        RAST._IType _out109;
        _out109 = (this).GenType(((m).dtor_outTypes).Select(_1636_typeI), DCOMP.GenTypeContext.@default());
        _1637_typeExpr = _out109;
        _1635_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1635_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1637_typeExpr));
        _1636_typeI = (_1636_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1638_visibility;
      _1638_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1639_typeParamsFiltered;
      _1639_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi30 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1640_typeParamI = BigInteger.Zero; _1640_typeParamI < _hi30; _1640_typeParamI++) {
        DAST._ITypeArgDecl _1641_typeParam;
        _1641_typeParam = ((m).dtor_typeParams).Select(_1640_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1641_typeParam).dtor_name)))) {
          _1639_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1639_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1641_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1642_typeParams;
      _1642_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1639_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi31 = new BigInteger((_1639_typeParamsFiltered).Count);
        for (BigInteger _1643_i = BigInteger.Zero; _1643_i < _hi31; _1643_i++) {
          DAST._IType _1644_typeArg;
          RAST._ITypeParamDecl _1645_rTypeParamDecl;
          DAST._IType _out110;
          RAST._ITypeParamDecl _out111;
          (this).GenTypeParam((_1639_typeParamsFiltered).Select(_1643_i), out _out110, out _out111);
          _1644_typeArg = _out110;
          _1645_rTypeParamDecl = _out111;
          var _pat_let_tv193 = _1645_rTypeParamDecl;
          _1645_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1645_rTypeParamDecl, _pat_let24_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let24_0, _1646_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>((_pat_let_tv193).dtor_constraints, _pat_let25_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let25_0, _1647_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1646_dt__update__tmp_h1).dtor_name, _1647_dt__update_hconstraints_h0)))));
          _1642_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1642_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1645_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1648_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1649_env = DCOMP.Environment.Default();
      RAST._IExpr _1650_preBody;
      _1650_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1651_preAssignNames;
      _1651_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1652_preAssignTypes;
      _1652_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1653_earlyReturn;
        _1653_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source84 = (m).dtor_outVars;
        bool unmatched84 = true;
        if (unmatched84) {
          if (_source84.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1654_outVars = _source84.dtor_value;
            unmatched84 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1653_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi32 = new BigInteger((_1654_outVars).Count);
                for (BigInteger _1655_outI = BigInteger.Zero; _1655_outI < _hi32; _1655_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1656_outVar;
                  _1656_outVar = (_1654_outVars).Select(_1655_outI);
                  Dafny.ISequence<Dafny.Rune> _1657_outName;
                  _1657_outName = DCOMP.__default.escapeVar(_1656_outVar);
                  Dafny.ISequence<Dafny.Rune> _1658_tracker__name;
                  _1658_tracker__name = DCOMP.__default.AddAssignedPrefix(_1657_outName);
                  _1651_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1651_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1658_tracker__name));
                  _1652_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1652_preAssignTypes, _1658_tracker__name, RAST.Type.create_Bool());
                  _1650_preBody = (_1650_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1658_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1659_tupleArgs;
                _1659_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi33 = new BigInteger((_1654_outVars).Count);
                for (BigInteger _1660_outI = BigInteger.Zero; _1660_outI < _hi33; _1660_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1661_outVar;
                  _1661_outVar = (_1654_outVars).Select(_1660_outI);
                  RAST._IType _1662_outType;
                  RAST._IType _out112;
                  _out112 = (this).GenType(((m).dtor_outTypes).Select(_1660_outI), DCOMP.GenTypeContext.@default());
                  _1662_outType = _out112;
                  Dafny.ISequence<Dafny.Rune> _1663_outName;
                  _1663_outName = DCOMP.__default.escapeVar(_1661_outVar);
                  _1620_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1620_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1663_outName));
                  RAST._IType _1664_outMaybeType;
                  _1664_outMaybeType = (((_1662_outType).CanReadWithoutClone()) ? (_1662_outType) : (RAST.__default.MaybePlaceboType(_1662_outType)));
                  _1621_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1621_paramTypes, _1663_outName, _1664_outMaybeType);
                  _1659_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1659_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1663_outName));
                }
                _1653_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_1659_tupleArgs);
              }
            }
          }
        }
        if (unmatched84) {
          unmatched84 = false;
        }
        _1649_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1651_preAssignNames, _1620_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1652_preAssignTypes, _1621_paramTypes));
        RAST._IExpr _1665_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1666___v71;
        DCOMP._IEnvironment _1667___v72;
        RAST._IExpr _out113;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out114;
        DCOMP._IEnvironment _out115;
        (this).GenStmts((m).dtor_body, _1627_selfIdent, _1649_env, true, _1653_earlyReturn, out _out113, out _out114, out _out115);
        _1665_body = _out113;
        _1666___v71 = _out114;
        _1667___v72 = _out115;
        _1648_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1650_preBody).Then(_1665_body));
      } else {
        _1649_env = DCOMP.Environment.create(_1620_paramNames, _1621_paramTypes);
        _1648_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1638_visibility, RAST.Fn.create(_1626_fnName, _1642_typeParams, _1619_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1635_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1635_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1635_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1648_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1668_declarations;
      _1668_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1669_i;
      _1669_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1670_stmts;
      _1670_stmts = stmts;
      while ((_1669_i) < (new BigInteger((_1670_stmts).Count))) {
        DAST._IStatement _1671_stmt;
        _1671_stmt = (_1670_stmts).Select(_1669_i);
        DAST._IStatement _source85 = _1671_stmt;
        bool unmatched85 = true;
        if (unmatched85) {
          if (_source85.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1672_name = _source85.dtor_name;
            DAST._IType _1673_optType = _source85.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source85.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched85 = false;
              if (((_1669_i) + (BigInteger.One)) < (new BigInteger((_1670_stmts).Count))) {
                DAST._IStatement _source86 = (_1670_stmts).Select((_1669_i) + (BigInteger.One));
                bool unmatched86 = true;
                if (unmatched86) {
                  if (_source86.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source86.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> _1674_name2 = lhs0.dtor_ident;
                      DAST._IExpression _1675_rhs = _source86.dtor_value;
                      unmatched86 = false;
                      if (object.Equals(_1674_name2, _1672_name)) {
                        _1670_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1670_stmts).Subsequence(BigInteger.Zero, _1669_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1672_name, _1673_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1675_rhs)))), (_1670_stmts).Drop((_1669_i) + (new BigInteger(2))));
                        _1671_stmt = (_1670_stmts).Select(_1669_i);
                      }
                    }
                  }
                }
                if (unmatched86) {
                  unmatched86 = false;
                }
              }
            }
          }
        }
        if (unmatched85) {
          unmatched85 = false;
        }
        RAST._IExpr _1676_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1677_recIdents;
        DCOMP._IEnvironment _1678_newEnv2;
        RAST._IExpr _out116;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
        DCOMP._IEnvironment _out118;
        (this).GenStmt(_1671_stmt, selfIdent, newEnv, (isLast) && ((_1669_i) == ((new BigInteger((_1670_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out116, out _out117, out _out118);
        _1676_stmtExpr = _out116;
        _1677_recIdents = _out117;
        _1678_newEnv2 = _out118;
        newEnv = _1678_newEnv2;
        DAST._IStatement _source87 = _1671_stmt;
        bool unmatched87 = true;
        if (unmatched87) {
          if (_source87.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1679_name = _source87.dtor_name;
            unmatched87 = false;
            {
              _1668_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1668_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_1679_name)));
            }
          }
        }
        if (unmatched87) {
          unmatched87 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1677_recIdents, _1668_declarations));
        generated = (generated).Then(_1676_stmtExpr);
        _1669_i = (_1669_i) + (BigInteger.One);
        if ((_1676_stmtExpr).is_Return) {
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
      DAST._IAssignLhs _source88 = lhs;
      bool unmatched88 = true;
      if (unmatched88) {
        if (_source88.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1680_id = _source88.dtor_ident;
          unmatched88 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1681_idRust;
            _1681_idRust = DCOMP.__default.escapeVar(_1680_id);
            if (((env).IsBorrowed(_1681_idRust)) || ((env).IsBorrowedMut(_1681_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1681_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1681_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1681_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched88) {
        if (_source88.is_Select) {
          DAST._IExpression _1682_on = _source88.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1683_field = _source88.dtor_field;
          unmatched88 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1684_fieldName;
            _1684_fieldName = DCOMP.__default.escapeVar(_1683_field);
            RAST._IExpr _1685_onExpr;
            DCOMP._IOwnership _1686_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1687_recIdents;
            RAST._IExpr _out119;
            DCOMP._IOwnership _out120;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
            (this).GenExpr(_1682_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out119, out _out120, out _out121);
            _1685_onExpr = _out119;
            _1686_onOwned = _out120;
            _1687_recIdents = _out121;
            RAST._IExpr _source89 = _1685_onExpr;
            bool unmatched89 = true;
            if (unmatched89) {
              bool disjunctiveMatch12 = false;
              if (_source89.is_Call) {
                RAST._IExpr obj2 = _source89.dtor_obj;
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
              if (_source89.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name6 = _source89.dtor_name;
                if (object.Equals(name6, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch12 = true;
                }
              }
              if (_source89.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op14 = _source89.dtor_op1;
                if (object.Equals(op14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying4 = _source89.dtor_underlying;
                  if (underlying4.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name7 = underlying4.dtor_name;
                    if (object.Equals(name7, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      disjunctiveMatch12 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch12) {
                unmatched89 = false;
                Dafny.ISequence<Dafny.Rune> _1688_isAssignedVar;
                _1688_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1684_fieldName);
                if (((newEnv).dtor_names).Contains(_1688_isAssignedVar)) {
                  generated = (((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1684_fieldName), RAST.Expr.create_Identifier(_1688_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1688_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1688_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1684_fieldName, rhs);
                }
              }
            }
            if (unmatched89) {
              unmatched89 = false;
              if (!object.Equals(_1685_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1685_onExpr = ((this).modify__macro).Apply1(_1685_onExpr);
              }
              generated = RAST.__default.AssignMember(_1685_onExpr, _1684_fieldName, rhs);
            }
            readIdents = _1687_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched88) {
        DAST._IExpression _1689_on = _source88.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1690_indices = _source88.dtor_indices;
        unmatched88 = false;
        {
          RAST._IExpr _1691_onExpr;
          DCOMP._IOwnership _1692_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1693_recIdents;
          RAST._IExpr _out122;
          DCOMP._IOwnership _out123;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
          (this).GenExpr(_1689_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out122, out _out123, out _out124);
          _1691_onExpr = _out122;
          _1692_onOwned = _out123;
          _1693_recIdents = _out124;
          readIdents = _1693_recIdents;
          _1691_onExpr = ((this).modify__macro).Apply1(_1691_onExpr);
          RAST._IExpr _1694_r;
          _1694_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1695_indicesExpr;
          _1695_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi34 = new BigInteger((_1690_indices).Count);
          for (BigInteger _1696_i = BigInteger.Zero; _1696_i < _hi34; _1696_i++) {
            RAST._IExpr _1697_idx;
            DCOMP._IOwnership _1698___v81;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1699_recIdentsIdx;
            RAST._IExpr _out125;
            DCOMP._IOwnership _out126;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out127;
            (this).GenExpr((_1690_indices).Select(_1696_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out125, out _out126, out _out127);
            _1697_idx = _out125;
            _1698___v81 = _out126;
            _1699_recIdentsIdx = _out127;
            Dafny.ISequence<Dafny.Rune> _1700_varName;
            _1700_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1696_i));
            _1695_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1695_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1700_varName)));
            _1694_r = (_1694_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1700_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1697_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1699_recIdentsIdx);
          }
          if ((new BigInteger((_1690_indices).Count)) > (BigInteger.One)) {
            _1691_onExpr = (_1691_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1701_rhs;
          _1701_rhs = rhs;
          var _pat_let_tv194 = env;
          if (((_1691_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1691_onExpr).LhsIdentifierName(), _pat_let26_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let26_0, _1702_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv194).GetType(_1702_name), _pat_let27_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let27_0, _1703_tpe => ((_1703_tpe).is_Some) && (((_1703_tpe).dtor_value).IsUninitArray())))))))) {
            _1701_rhs = RAST.__default.MaybeUninitNew(_1701_rhs);
          }
          generated = (_1694_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1691_onExpr, _1695_indicesExpr)), _1701_rhs));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source90 = stmt;
      bool unmatched90 = true;
      if (unmatched90) {
        if (_source90.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1704_fields = _source90.dtor_fields;
          unmatched90 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi35 = new BigInteger((_1704_fields).Count);
            for (BigInteger _1705_i = BigInteger.Zero; _1705_i < _hi35; _1705_i++) {
              DAST._IFormal _1706_field;
              _1706_field = (_1704_fields).Select(_1705_i);
              Dafny.ISequence<Dafny.Rune> _1707_fieldName;
              _1707_fieldName = DCOMP.__default.escapeVar((_1706_field).dtor_name);
              RAST._IType _1708_fieldTyp;
              RAST._IType _out128;
              _out128 = (this).GenType((_1706_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1708_fieldTyp = _out128;
              Dafny.ISequence<Dafny.Rune> _1709_isAssignedVar;
              _1709_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1707_fieldName);
              if (((newEnv).dtor_names).Contains(_1709_isAssignedVar)) {
                RAST._IExpr _1710_rhs;
                DCOMP._IOwnership _1711___v82;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1712___v83;
                RAST._IExpr _out129;
                DCOMP._IOwnership _out130;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1706_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out129, out _out130, out _out131);
                _1710_rhs = _out129;
                _1711___v82 = _out130;
                _1712___v83 = _out131;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1709_isAssignedVar));
                generated = (generated).Then((((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1707_fieldName), RAST.Expr.create_Identifier(_1709_isAssignedVar), _1710_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1709_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1713_name = _source90.dtor_name;
          DAST._IType _1714_typ = _source90.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source90.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1715_expression = maybeValue1.dtor_value;
            unmatched90 = false;
            {
              RAST._IType _1716_tpe;
              RAST._IType _out132;
              _out132 = (this).GenType(_1714_typ, DCOMP.GenTypeContext.@default());
              _1716_tpe = _out132;
              Dafny.ISequence<Dafny.Rune> _1717_varName;
              _1717_varName = DCOMP.__default.escapeVar(_1713_name);
              bool _1718_hasCopySemantics;
              _1718_hasCopySemantics = (_1716_tpe).CanReadWithoutClone();
              if (((_1715_expression).is_InitializationValue) && (!(_1718_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1717_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.MaybePlaceboPath).AsExpr()).ApplyType1(_1716_tpe)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1717_varName, RAST.__default.MaybePlaceboType(_1716_tpe));
              } else {
                RAST._IExpr _1719_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1720_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1715_expression).is_InitializationValue) && ((_1716_tpe).IsObjectOrPointer())) {
                  _1719_expr = (_1716_tpe).ToNullExpr();
                  _1720_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1721_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out133;
                  DCOMP._IOwnership _out134;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
                  (this).GenExpr(_1715_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
                  _1719_expr = _out133;
                  _1721_exprOwnership = _out134;
                  _1720_recIdents = _out135;
                }
                readIdents = _1720_recIdents;
                _1716_tpe = (((_1715_expression).is_NewUninitArray) ? ((_1716_tpe).TypeAtInitialization()) : (_1716_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1717_varName, Std.Wrappers.Option<RAST._IType>.create_Some(_1716_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1719_expr));
                newEnv = (env).AddAssigned(_1717_varName, _1716_tpe);
              }
            }
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1722_name = _source90.dtor_name;
          DAST._IType _1723_typ = _source90.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source90.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched90 = false;
            {
              DAST._IStatement _1724_newStmt;
              _1724_newStmt = DAST.Statement.create_DeclareVar(_1722_name, _1723_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1723_typ)));
              RAST._IExpr _out136;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
              DCOMP._IEnvironment _out138;
              (this).GenStmt(_1724_newStmt, selfIdent, env, isLast, earlyReturn, out _out136, out _out137, out _out138);
              generated = _out136;
              readIdents = _out137;
              newEnv = _out138;
            }
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Assign) {
          DAST._IAssignLhs _1725_lhs = _source90.dtor_lhs;
          DAST._IExpression _1726_expression = _source90.dtor_value;
          unmatched90 = false;
          {
            RAST._IExpr _1727_exprGen;
            DCOMP._IOwnership _1728___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1729_exprIdents;
            RAST._IExpr _out139;
            DCOMP._IOwnership _out140;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
            (this).GenExpr(_1726_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out139, out _out140, out _out141);
            _1727_exprGen = _out139;
            _1728___v84 = _out140;
            _1729_exprIdents = _out141;
            if ((_1725_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1730_rustId;
              _1730_rustId = DCOMP.__default.escapeVar((_1725_lhs).dtor_ident);
              Std.Wrappers._IOption<RAST._IType> _1731_tpe;
              _1731_tpe = (env).GetType(_1730_rustId);
              if (((_1731_tpe).is_Some) && ((((_1731_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1727_exprGen = RAST.__default.MaybePlacebo(_1727_exprGen);
              }
            }
            if (((_1725_lhs).is_Index) && (((_1725_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1732_rustId;
              _1732_rustId = DCOMP.__default.escapeVar(((_1725_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1733_tpe;
              _1733_tpe = (env).GetType(_1732_rustId);
              if (((_1733_tpe).is_Some) && ((((_1733_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1727_exprGen = RAST.__default.MaybeUninitNew(_1727_exprGen);
              }
            }
            RAST._IExpr _1734_lhsGen;
            bool _1735_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1736_recIdents;
            DCOMP._IEnvironment _1737_resEnv;
            RAST._IExpr _out142;
            bool _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            DCOMP._IEnvironment _out145;
            (this).GenAssignLhs(_1725_lhs, _1727_exprGen, selfIdent, env, out _out142, out _out143, out _out144, out _out145);
            _1734_lhsGen = _out142;
            _1735_needsIIFE = _out143;
            _1736_recIdents = _out144;
            _1737_resEnv = _out145;
            generated = _1734_lhsGen;
            newEnv = _1737_resEnv;
            if (_1735_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1736_recIdents, _1729_exprIdents);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_If) {
          DAST._IExpression _1738_cond = _source90.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1739_thnDafny = _source90.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1740_elsDafny = _source90.dtor_els;
          unmatched90 = false;
          {
            RAST._IExpr _1741_cond;
            DCOMP._IOwnership _1742___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1743_recIdents;
            RAST._IExpr _out146;
            DCOMP._IOwnership _out147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
            (this).GenExpr(_1738_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out146, out _out147, out _out148);
            _1741_cond = _out146;
            _1742___v85 = _out147;
            _1743_recIdents = _out148;
            Dafny.ISequence<Dafny.Rune> _1744_condString;
            _1744_condString = (_1741_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1743_recIdents;
            RAST._IExpr _1745_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1746_thnIdents;
            DCOMP._IEnvironment _1747_thnEnv;
            RAST._IExpr _out149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out150;
            DCOMP._IEnvironment _out151;
            (this).GenStmts(_1739_thnDafny, selfIdent, env, isLast, earlyReturn, out _out149, out _out150, out _out151);
            _1745_thn = _out149;
            _1746_thnIdents = _out150;
            _1747_thnEnv = _out151;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1746_thnIdents);
            RAST._IExpr _1748_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1749_elsIdents;
            DCOMP._IEnvironment _1750_elsEnv;
            RAST._IExpr _out152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
            DCOMP._IEnvironment _out154;
            (this).GenStmts(_1740_elsDafny, selfIdent, env, isLast, earlyReturn, out _out152, out _out153, out _out154);
            _1748_els = _out152;
            _1749_elsIdents = _out153;
            _1750_elsEnv = _out154;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1749_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1741_cond, _1745_thn, _1748_els);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1751_lbl = _source90.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1752_body = _source90.dtor_body;
          unmatched90 = false;
          {
            RAST._IExpr _1753_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1754_bodyIdents;
            DCOMP._IEnvironment _1755_env2;
            RAST._IExpr _out155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
            DCOMP._IEnvironment _out157;
            (this).GenStmts(_1752_body, selfIdent, env, isLast, earlyReturn, out _out155, out _out156, out _out157);
            _1753_body = _out155;
            _1754_bodyIdents = _out156;
            _1755_env2 = _out157;
            readIdents = _1754_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1751_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1753_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_While) {
          DAST._IExpression _1756_cond = _source90.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1757_body = _source90.dtor_body;
          unmatched90 = false;
          {
            RAST._IExpr _1758_cond;
            DCOMP._IOwnership _1759___v86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1760_recIdents;
            RAST._IExpr _out158;
            DCOMP._IOwnership _out159;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
            (this).GenExpr(_1756_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out158, out _out159, out _out160);
            _1758_cond = _out158;
            _1759___v86 = _out159;
            _1760_recIdents = _out160;
            readIdents = _1760_recIdents;
            RAST._IExpr _1761_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1762_bodyIdents;
            DCOMP._IEnvironment _1763_bodyEnv;
            RAST._IExpr _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            DCOMP._IEnvironment _out163;
            (this).GenStmts(_1757_body, selfIdent, env, false, earlyReturn, out _out161, out _out162, out _out163);
            _1761_bodyExpr = _out161;
            _1762_bodyIdents = _out162;
            _1763_bodyEnv = _out163;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1762_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1758_cond), _1761_bodyExpr);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1764_boundName = _source90.dtor_boundName;
          DAST._IType _1765_boundType = _source90.dtor_boundType;
          DAST._IExpression _1766_overExpr = _source90.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1767_body = _source90.dtor_body;
          unmatched90 = false;
          {
            RAST._IExpr _1768_over;
            DCOMP._IOwnership _1769___v87;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1770_recIdents;
            RAST._IExpr _out164;
            DCOMP._IOwnership _out165;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out166;
            (this).GenExpr(_1766_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out164, out _out165, out _out166);
            _1768_over = _out164;
            _1769___v87 = _out165;
            _1770_recIdents = _out166;
            if (((_1766_overExpr).is_MapBoundedPool) || ((_1766_overExpr).is_SetBoundedPool)) {
              _1768_over = ((_1768_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1771_boundTpe;
            RAST._IType _out167;
            _out167 = (this).GenType(_1765_boundType, DCOMP.GenTypeContext.@default());
            _1771_boundTpe = _out167;
            readIdents = _1770_recIdents;
            Dafny.ISequence<Dafny.Rune> _1772_boundRName;
            _1772_boundRName = DCOMP.__default.escapeVar(_1764_boundName);
            RAST._IExpr _1773_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1774_bodyIdents;
            DCOMP._IEnvironment _1775_bodyEnv;
            RAST._IExpr _out168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
            DCOMP._IEnvironment _out170;
            (this).GenStmts(_1767_body, selfIdent, (env).AddAssigned(_1772_boundRName, _1771_boundTpe), false, earlyReturn, out _out168, out _out169, out _out170);
            _1773_bodyExpr = _out168;
            _1774_bodyIdents = _out169;
            _1775_bodyEnv = _out170;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1774_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1772_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1772_boundRName, _1768_over, _1773_bodyExpr);
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1776_toLabel = _source90.dtor_toLabel;
          unmatched90 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source91 = _1776_toLabel;
            bool unmatched91 = true;
            if (unmatched91) {
              if (_source91.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1777_lbl = _source91.dtor_value;
                unmatched91 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1777_lbl)));
                }
              }
            }
            if (unmatched91) {
              unmatched91 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1778_body = _source90.dtor_body;
          unmatched90 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1779_selfClone;
              DCOMP._IOwnership _1780___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1781___v89;
              RAST._IExpr _out171;
              DCOMP._IOwnership _out172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out171, out _out172, out _out173);
              _1779_selfClone = _out171;
              _1780___v88 = _out172;
              _1781___v89 = _out173;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1779_selfClone)));
            }
            newEnv = env;
            RAST._IExpr _1782_loopBegin;
            _1782_loopBegin = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi36 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1783_paramI = BigInteger.Zero; _1783_paramI < _hi36; _1783_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1784_param;
              _1784_param = ((env).dtor_names).Select(_1783_paramI);
              RAST._IExpr _1785_paramInit;
              DCOMP._IOwnership _1786___v90;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1787___v91;
              RAST._IExpr _out174;
              DCOMP._IOwnership _out175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out176;
              (this).GenIdent(_1784_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out174, out _out175, out _out176);
              _1785_paramInit = _out174;
              _1786___v90 = _out175;
              _1787___v91 = _out176;
              Dafny.ISequence<Dafny.Rune> _1788_recVar;
              _1788_recVar = Dafny.Sequence<Dafny.Rune>.Concat(DCOMP.COMP.TailRecursionPrefix, Std.Strings.__default.OfNat(_1783_paramI));
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1788_recVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1785_paramInit)));
              if (((env).dtor_types).Contains(_1784_param)) {
                RAST._IType _1789_declaredType;
                _1789_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1784_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1784_param, _1789_declaredType);
                newEnv = (newEnv).AddAssigned(_1788_recVar, _1789_declaredType);
              }
              _1782_loopBegin = (_1782_loopBegin).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1784_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Identifier(_1788_recVar))));
            }
            RAST._IExpr _1790_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1791_bodyIdents;
            DCOMP._IEnvironment _1792_bodyEnv;
            RAST._IExpr _out177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out178;
            DCOMP._IEnvironment _out179;
            (this).GenStmts(_1778_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out177, out _out178, out _out179);
            _1790_bodyExpr = _out177;
            _1791_bodyIdents = _out178;
            _1792_bodyEnv = _out179;
            readIdents = _1791_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), (_1782_loopBegin).Then(_1790_bodyExpr))));
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_JumpTailCallStart) {
          unmatched90 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Call) {
          DAST._IExpression _1793_on = _source90.dtor_on;
          DAST._ICallName _1794_name = _source90.dtor_callName;
          Dafny.ISequence<DAST._IType> _1795_typeArgs = _source90.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1796_args = _source90.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1797_maybeOutVars = _source90.dtor_outs;
          unmatched90 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1798_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1799_recIdents;
            Dafny.ISequence<RAST._IType> _1800_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1801_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out181;
            Dafny.ISequence<RAST._IType> _out182;
            Std.Wrappers._IOption<DAST._IResolvedType> _out183;
            (this).GenArgs(selfIdent, _1794_name, _1795_typeArgs, _1796_args, env, out _out180, out _out181, out _out182, out _out183);
            _1798_argExprs = _out180;
            _1799_recIdents = _out181;
            _1800_typeExprs = _out182;
            _1801_fullNameQualifier = _out183;
            readIdents = _1799_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source92 = _1801_fullNameQualifier;
            bool unmatched92 = true;
            if (unmatched92) {
              if (_source92.is_Some) {
                DAST._IResolvedType value9 = _source92.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1802_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1803_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1804_base = value9.dtor_kind;
                unmatched92 = false;
                RAST._IExpr _1805_fullPath;
                RAST._IExpr _out184;
                _out184 = DCOMP.COMP.GenPathExpr(_1802_path, true);
                _1805_fullPath = _out184;
                Dafny.ISequence<RAST._IType> _1806_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out185;
                _out185 = (this).GenTypeArgs(_1803_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1806_onTypeExprs = _out185;
                RAST._IExpr _1807_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1808_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1809_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1804_base).is_Trait) || ((_1804_base).is_Class)) {
                  RAST._IExpr _out186;
                  DCOMP._IOwnership _out187;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out188;
                  (this).GenExpr(_1793_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out186, out _out187, out _out188);
                  _1807_onExpr = _out186;
                  _1808_recOwnership = _out187;
                  _1809_recIdents = _out188;
                  _1807_onExpr = ((this).modify__macro).Apply1(_1807_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1809_recIdents);
                } else {
                  RAST._IExpr _out189;
                  DCOMP._IOwnership _out190;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out191;
                  (this).GenExpr(_1793_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out189, out _out190, out _out191);
                  _1807_onExpr = _out189;
                  _1808_recOwnership = _out190;
                  _1809_recIdents = _out191;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1809_recIdents);
                }
                generated = ((((_1805_fullPath).ApplyType(_1806_onTypeExprs)).FSel(DCOMP.__default.escapeName((_1794_name).dtor_name))).ApplyType(_1800_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1807_onExpr), _1798_argExprs));
              }
            }
            if (unmatched92) {
              unmatched92 = false;
              RAST._IExpr _1810_onExpr;
              DCOMP._IOwnership _1811___v96;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1812_enclosingIdents;
              RAST._IExpr _out192;
              DCOMP._IOwnership _out193;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
              (this).GenExpr(_1793_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out192, out _out193, out _out194);
              _1810_onExpr = _out192;
              _1811___v96 = _out193;
              _1812_enclosingIdents = _out194;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1812_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1813_renderedName;
              _1813_renderedName = (this).GetMethodName(_1793_on, _1794_name);
              DAST._IExpression _source93 = _1793_on;
              bool unmatched93 = true;
              if (unmatched93) {
                bool disjunctiveMatch13 = false;
                if (_source93.is_Companion) {
                  disjunctiveMatch13 = true;
                }
                if (_source93.is_ExternCompanion) {
                  disjunctiveMatch13 = true;
                }
                if (disjunctiveMatch13) {
                  unmatched93 = false;
                  {
                    _1810_onExpr = (_1810_onExpr).FSel(_1813_renderedName);
                  }
                }
              }
              if (unmatched93) {
                unmatched93 = false;
                {
                  if (!object.Equals(_1810_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source94 = _1794_name;
                    bool unmatched94 = true;
                    if (unmatched94) {
                      if (_source94.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source94.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1814_tpe = onType0.dtor_value;
                          unmatched94 = false;
                          RAST._IType _1815_typ;
                          RAST._IType _out195;
                          _out195 = (this).GenType(_1814_tpe, DCOMP.GenTypeContext.@default());
                          _1815_typ = _out195;
                          if (((_1815_typ).IsObjectOrPointer()) && (!object.Equals(_1810_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1810_onExpr = ((this).modify__macro).Apply1(_1810_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched94) {
                      unmatched94 = false;
                    }
                  }
                  _1810_onExpr = (_1810_onExpr).Sel(_1813_renderedName);
                }
              }
              generated = ((_1810_onExpr).ApplyType(_1800_typeExprs)).Apply(_1798_argExprs);
            }
            if (((_1797_maybeOutVars).is_Some) && ((new BigInteger(((_1797_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1816_outVar;
              _1816_outVar = DCOMP.__default.escapeVar(((_1797_maybeOutVars).dtor_value).Select(BigInteger.Zero));
              if (!((env).CanReadWithoutClone(_1816_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1816_outVar, generated);
            } else if (((_1797_maybeOutVars).is_None) || ((new BigInteger(((_1797_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1817_tmpVar;
              _1817_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1818_tmpId;
              _1818_tmpId = RAST.Expr.create_Identifier(_1817_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1817_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1819_outVars;
              _1819_outVars = (_1797_maybeOutVars).dtor_value;
              BigInteger _hi37 = new BigInteger((_1819_outVars).Count);
              for (BigInteger _1820_outI = BigInteger.Zero; _1820_outI < _hi37; _1820_outI++) {
                Dafny.ISequence<Dafny.Rune> _1821_outVar;
                _1821_outVar = DCOMP.__default.escapeVar((_1819_outVars).Select(_1820_outI));
                RAST._IExpr _1822_rhs;
                _1822_rhs = (_1818_tmpId).Sel(Std.Strings.__default.OfNat(_1820_outI));
                if (!((env).CanReadWithoutClone(_1821_outVar))) {
                  _1822_rhs = RAST.__default.MaybePlacebo(_1822_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1821_outVar, _1822_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Return) {
          DAST._IExpression _1823_exprDafny = _source90.dtor_expr;
          unmatched90 = false;
          {
            RAST._IExpr _1824_expr;
            DCOMP._IOwnership _1825___v106;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1826_recIdents;
            RAST._IExpr _out196;
            DCOMP._IOwnership _out197;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out198;
            (this).GenExpr(_1823_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out196, out _out197, out _out198);
            _1824_expr = _out196;
            _1825___v106 = _out197;
            _1826_recIdents = _out198;
            readIdents = _1826_recIdents;
            if (isLast) {
              generated = _1824_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1824_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_EarlyReturn) {
          unmatched90 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source95 = earlyReturn;
            bool unmatched95 = true;
            if (unmatched95) {
              if (_source95.is_None) {
                unmatched95 = false;
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
              }
            }
            if (unmatched95) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1827_rustIdents = _source95.dtor_value;
              unmatched95 = false;
              Dafny.ISequence<RAST._IExpr> _1828_tupleArgs;
              _1828_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi38 = new BigInteger((_1827_rustIdents).Count);
              for (BigInteger _1829_i = BigInteger.Zero; _1829_i < _hi38; _1829_i++) {
                RAST._IExpr _1830_rIdent;
                DCOMP._IOwnership _1831___v107;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1832___v108;
                RAST._IExpr _out199;
                DCOMP._IOwnership _out200;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
                (this).GenIdent((_1827_rustIdents).Select(_1829_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out199, out _out200, out _out201);
                _1830_rIdent = _out199;
                _1831___v107 = _out200;
                _1832___v108 = _out201;
                _1828_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1828_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1830_rIdent));
              }
              if ((new BigInteger((_1828_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1828_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1828_tupleArgs)));
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Halt) {
          unmatched90 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched90) {
        DAST._IExpression _1833_e = _source90.dtor_Print_a0;
        unmatched90 = false;
        {
          RAST._IExpr _1834_printedExpr;
          DCOMP._IOwnership _1835_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1836_recIdents;
          RAST._IExpr _out202;
          DCOMP._IOwnership _out203;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out204;
          (this).GenExpr(_1833_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out202, out _out203, out _out204);
          _1834_printedExpr = _out202;
          _1835_recOwnership = _out203;
          _1836_recIdents = _out204;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).AsExpr()).Apply1(_1834_printedExpr)));
          readIdents = _1836_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeRangeToRustType(DAST._INewtypeRange range) {
      DAST._INewtypeRange _source96 = range;
      bool unmatched96 = true;
      if (unmatched96) {
        if (_source96.is_NoRange) {
          unmatched96 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched96) {
        if (_source96.is_U8) {
          unmatched96 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched96) {
        if (_source96.is_U16) {
          unmatched96 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched96) {
        if (_source96.is_U32) {
          unmatched96 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched96) {
        if (_source96.is_U64) {
          unmatched96 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched96) {
        if (_source96.is_U128) {
          unmatched96 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched96) {
        if (_source96.is_I8) {
          unmatched96 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched96) {
        if (_source96.is_I16) {
          unmatched96 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched96) {
        if (_source96.is_I32) {
          unmatched96 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched96) {
        if (_source96.is_I64) {
          unmatched96 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched96) {
        if (_source96.is_I128) {
          unmatched96 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched96) {
        unmatched96 = false;
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
      DAST._IExpression _source97 = e;
      bool unmatched97 = true;
      if (unmatched97) {
        if (_source97.is_Literal) {
          DAST._ILiteral _h170 = _source97.dtor_Literal_a0;
          if (_h170.is_BoolLiteral) {
            bool _1837_b = _h170.dtor_BoolLiteral_a0;
            unmatched97 = false;
            {
              RAST._IExpr _out209;
              DCOMP._IOwnership _out210;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1837_b), expectedOwnership, out _out209, out _out210);
              r = _out209;
              resultingOwnership = _out210;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched97) {
        if (_source97.is_Literal) {
          DAST._ILiteral _h171 = _source97.dtor_Literal_a0;
          if (_h171.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1838_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1839_t = _h171.dtor_IntLiteral_a1;
            unmatched97 = false;
            {
              DAST._IType _source98 = _1839_t;
              bool unmatched98 = true;
              if (unmatched98) {
                if (_source98.is_Primitive) {
                  DAST._IPrimitive _h70 = _source98.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched98 = false;
                    {
                      if ((new BigInteger((_1838_i).Count)) <= (new BigInteger(4))) {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralInt(_1838_i));
                      } else {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1838_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched98) {
                DAST._IType _1840_o = _source98;
                unmatched98 = false;
                {
                  RAST._IType _1841_genType;
                  RAST._IType _out211;
                  _out211 = (this).GenType(_1840_o, DCOMP.GenTypeContext.@default());
                  _1841_genType = _out211;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1838_i), _1841_genType);
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
      if (unmatched97) {
        if (_source97.is_Literal) {
          DAST._ILiteral _h172 = _source97.dtor_Literal_a0;
          if (_h172.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1842_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1843_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1844_t = _h172.dtor_DecLiteral_a2;
            unmatched97 = false;
            {
              DAST._IType _source99 = _1844_t;
              bool unmatched99 = true;
              if (unmatched99) {
                if (_source99.is_Primitive) {
                  DAST._IPrimitive _h71 = _source99.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched99 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1842_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1843_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched99) {
                DAST._IType _1845_o = _source99;
                unmatched99 = false;
                {
                  RAST._IType _1846_genType;
                  RAST._IType _out214;
                  _out214 = (this).GenType(_1845_o, DCOMP.GenTypeContext.@default());
                  _1846_genType = _out214;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1842_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1843_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1846_genType);
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
      if (unmatched97) {
        if (_source97.is_Literal) {
          DAST._ILiteral _h173 = _source97.dtor_Literal_a0;
          if (_h173.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1847_l = _h173.dtor_StringLiteral_a0;
            bool _1848_verbatim = _h173.dtor_verbatim;
            unmatched97 = false;
            {
              r = (((RAST.__default.dafny__runtime).MSel((this).string__of)).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1847_l, false, _1848_verbatim));
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
      if (unmatched97) {
        if (_source97.is_Literal) {
          DAST._ILiteral _h174 = _source97.dtor_Literal_a0;
          if (_h174.is_CharLiteralUTF16) {
            BigInteger _1849_c = _h174.dtor_CharLiteralUTF16_a0;
            unmatched97 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1849_c));
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
      if (unmatched97) {
        if (_source97.is_Literal) {
          DAST._ILiteral _h175 = _source97.dtor_Literal_a0;
          if (_h175.is_CharLiteral) {
            Dafny.Rune _1850_c = _h175.dtor_CharLiteral_a0;
            unmatched97 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1850_c).Value)));
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
      if (unmatched97) {
        DAST._ILiteral _h176 = _source97.dtor_Literal_a0;
        DAST._IType _1851_tpe = _h176.dtor_Null_a0;
        unmatched97 = false;
        {
          RAST._IType _1852_tpeGen;
          RAST._IType _out223;
          _out223 = (this).GenType(_1851_tpe, DCOMP.GenTypeContext.@default());
          _1852_tpeGen = _out223;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null_mut"));
          } else {
            r = RAST.Expr.create_TypeAscription((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1852_tpeGen);
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
      DAST._IBinOp _1853_op = _let_tmp_rhs56.dtor_op;
      DAST._IExpression _1854_lExpr = _let_tmp_rhs56.dtor_left;
      DAST._IExpression _1855_rExpr = _let_tmp_rhs56.dtor_right;
      DAST.Format._IBinaryOpFormat _1856_format = _let_tmp_rhs56.dtor_format2;
      bool _1857_becomesLeftCallsRight;
      _1857_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source100 = _1853_op;
        bool unmatched100 = true;
        if (unmatched100) {
          bool disjunctiveMatch14 = false;
          if (_source100.is_SetMerge) {
            disjunctiveMatch14 = true;
          }
          if (_source100.is_SetSubtraction) {
            disjunctiveMatch14 = true;
          }
          if (_source100.is_SetIntersection) {
            disjunctiveMatch14 = true;
          }
          if (_source100.is_SetDisjoint) {
            disjunctiveMatch14 = true;
          }
          if (_source100.is_MapMerge) {
            disjunctiveMatch14 = true;
          }
          if (_source100.is_MapSubtraction) {
            disjunctiveMatch14 = true;
          }
          if (_source100.is_MultisetMerge) {
            disjunctiveMatch14 = true;
          }
          if (_source100.is_MultisetSubtraction) {
            disjunctiveMatch14 = true;
          }
          if (_source100.is_MultisetIntersection) {
            disjunctiveMatch14 = true;
          }
          if (_source100.is_MultisetDisjoint) {
            disjunctiveMatch14 = true;
          }
          if (_source100.is_Concat) {
            disjunctiveMatch14 = true;
          }
          if (disjunctiveMatch14) {
            unmatched100 = false;
            return true;
          }
        }
        if (unmatched100) {
          unmatched100 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1858_becomesRightCallsLeft;
      _1858_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source101 = _1853_op;
        bool unmatched101 = true;
        if (unmatched101) {
          if (_source101.is_In) {
            unmatched101 = false;
            return true;
          }
        }
        if (unmatched101) {
          unmatched101 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1859_becomesCallLeftRight;
      _1859_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source102 = _1853_op;
        bool unmatched102 = true;
        if (unmatched102) {
          if (_source102.is_Eq) {
            bool referential0 = _source102.dtor_referential;
            if ((referential0) == (true)) {
              unmatched102 = false;
              return false;
            }
          }
        }
        if (unmatched102) {
          if (_source102.is_SetMerge) {
            unmatched102 = false;
            return true;
          }
        }
        if (unmatched102) {
          if (_source102.is_SetSubtraction) {
            unmatched102 = false;
            return true;
          }
        }
        if (unmatched102) {
          if (_source102.is_SetIntersection) {
            unmatched102 = false;
            return true;
          }
        }
        if (unmatched102) {
          if (_source102.is_SetDisjoint) {
            unmatched102 = false;
            return true;
          }
        }
        if (unmatched102) {
          if (_source102.is_MapMerge) {
            unmatched102 = false;
            return true;
          }
        }
        if (unmatched102) {
          if (_source102.is_MapSubtraction) {
            unmatched102 = false;
            return true;
          }
        }
        if (unmatched102) {
          if (_source102.is_MultisetMerge) {
            unmatched102 = false;
            return true;
          }
        }
        if (unmatched102) {
          if (_source102.is_MultisetSubtraction) {
            unmatched102 = false;
            return true;
          }
        }
        if (unmatched102) {
          if (_source102.is_MultisetIntersection) {
            unmatched102 = false;
            return true;
          }
        }
        if (unmatched102) {
          if (_source102.is_MultisetDisjoint) {
            unmatched102 = false;
            return true;
          }
        }
        if (unmatched102) {
          if (_source102.is_Concat) {
            unmatched102 = false;
            return true;
          }
        }
        if (unmatched102) {
          unmatched102 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1860_expectedLeftOwnership;
      _1860_expectedLeftOwnership = ((_1857_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1858_becomesRightCallsLeft) || (_1859_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1861_expectedRightOwnership;
      _1861_expectedRightOwnership = (((_1857_becomesLeftCallsRight) || (_1859_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1858_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1862_left;
      DCOMP._IOwnership _1863___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1864_recIdentsL;
      RAST._IExpr _out226;
      DCOMP._IOwnership _out227;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
      (this).GenExpr(_1854_lExpr, selfIdent, env, _1860_expectedLeftOwnership, out _out226, out _out227, out _out228);
      _1862_left = _out226;
      _1863___v113 = _out227;
      _1864_recIdentsL = _out228;
      RAST._IExpr _1865_right;
      DCOMP._IOwnership _1866___v114;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1867_recIdentsR;
      RAST._IExpr _out229;
      DCOMP._IOwnership _out230;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out231;
      (this).GenExpr(_1855_rExpr, selfIdent, env, _1861_expectedRightOwnership, out _out229, out _out230, out _out231);
      _1865_right = _out229;
      _1866___v114 = _out230;
      _1867_recIdentsR = _out231;
      DAST._IBinOp _source103 = _1853_op;
      bool unmatched103 = true;
      if (unmatched103) {
        if (_source103.is_In) {
          unmatched103 = false;
          {
            r = ((_1865_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1862_left);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_SeqProperPrefix) {
          unmatched103 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1862_left, _1865_right, _1856_format);
        }
      }
      if (unmatched103) {
        if (_source103.is_SeqPrefix) {
          unmatched103 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1862_left, _1865_right, _1856_format);
        }
      }
      if (unmatched103) {
        if (_source103.is_SetMerge) {
          unmatched103 = false;
          {
            r = ((_1862_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1865_right);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_SetSubtraction) {
          unmatched103 = false;
          {
            r = ((_1862_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1865_right);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_SetIntersection) {
          unmatched103 = false;
          {
            r = ((_1862_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1865_right);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_Subset) {
          unmatched103 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1862_left, _1865_right, _1856_format);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_ProperSubset) {
          unmatched103 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1862_left, _1865_right, _1856_format);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_SetDisjoint) {
          unmatched103 = false;
          {
            r = ((_1862_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1865_right);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_MapMerge) {
          unmatched103 = false;
          {
            r = ((_1862_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1865_right);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_MapSubtraction) {
          unmatched103 = false;
          {
            r = ((_1862_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1865_right);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_MultisetMerge) {
          unmatched103 = false;
          {
            r = ((_1862_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1865_right);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_MultisetSubtraction) {
          unmatched103 = false;
          {
            r = ((_1862_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1865_right);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_MultisetIntersection) {
          unmatched103 = false;
          {
            r = ((_1862_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1865_right);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_Submultiset) {
          unmatched103 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1862_left, _1865_right, _1856_format);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_ProperSubmultiset) {
          unmatched103 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1862_left, _1865_right, _1856_format);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_MultisetDisjoint) {
          unmatched103 = false;
          {
            r = ((_1862_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1865_right);
          }
        }
      }
      if (unmatched103) {
        if (_source103.is_Concat) {
          unmatched103 = false;
          {
            r = ((_1862_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1865_right);
          }
        }
      }
      if (unmatched103) {
        unmatched103 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1853_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1853_op), _1862_left, _1865_right, _1856_format);
          } else {
            DAST._IBinOp _source104 = _1853_op;
            bool unmatched104 = true;
            if (unmatched104) {
              if (_source104.is_Eq) {
                bool _1868_referential = _source104.dtor_referential;
                unmatched104 = false;
                {
                  if (_1868_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1862_left, _1865_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1855_rExpr).is_SeqValue) && ((new BigInteger(((_1855_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1862_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1854_lExpr).is_SeqValue) && ((new BigInteger(((_1854_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1865_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1862_left, _1865_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched104) {
              if (_source104.is_EuclidianDiv) {
                unmatched104 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1862_left, _1865_right));
                }
              }
            }
            if (unmatched104) {
              if (_source104.is_EuclidianMod) {
                unmatched104 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1862_left, _1865_right));
                }
              }
            }
            if (unmatched104) {
              Dafny.ISequence<Dafny.Rune> _1869_op = _source104.dtor_Passthrough_a0;
              unmatched104 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1869_op, _1862_left, _1865_right, _1856_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1864_recIdentsL, _1867_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs57 = e;
      DAST._IExpression _1870_expr = _let_tmp_rhs57.dtor_value;
      DAST._IType _1871_fromTpe = _let_tmp_rhs57.dtor_from;
      DAST._IType _1872_toTpe = _let_tmp_rhs57.dtor_typ;
      DAST._IType _let_tmp_rhs58 = _1872_toTpe;
      DAST._IResolvedType _let_tmp_rhs59 = _let_tmp_rhs58.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1873_path = _let_tmp_rhs59.dtor_path;
      Dafny.ISequence<DAST._IType> _1874_typeArgs = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs60 = _let_tmp_rhs59.dtor_kind;
      DAST._IType _1875_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _1876_range = _let_tmp_rhs60.dtor_range;
      bool _1877_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1878___v116 = _let_tmp_rhs59.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1879___v117 = _let_tmp_rhs59.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1880___v118 = _let_tmp_rhs59.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1881_nativeToType;
      _1881_nativeToType = DCOMP.COMP.NewtypeRangeToRustType(_1876_range);
      if (object.Equals(_1871_fromTpe, _1875_b)) {
        RAST._IExpr _1882_recursiveGen;
        DCOMP._IOwnership _1883_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1884_recIdents;
        RAST._IExpr _out234;
        DCOMP._IOwnership _out235;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out236;
        (this).GenExpr(_1870_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out234, out _out235, out _out236);
        _1882_recursiveGen = _out234;
        _1883_recOwned = _out235;
        _1884_recIdents = _out236;
        readIdents = _1884_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source105 = _1881_nativeToType;
        bool unmatched105 = true;
        if (unmatched105) {
          if (_source105.is_Some) {
            RAST._IType _1885_v = _source105.dtor_value;
            unmatched105 = false;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1882_recursiveGen, RAST.Expr.create_ExprFromType(_1885_v)));
            RAST._IExpr _out237;
            DCOMP._IOwnership _out238;
            (this).FromOwned(r, expectedOwnership, out _out237, out _out238);
            r = _out237;
            resultingOwnership = _out238;
          }
        }
        if (unmatched105) {
          unmatched105 = false;
          if (_1877_erase) {
            r = _1882_recursiveGen;
          } else {
            RAST._IType _1886_rhsType;
            RAST._IType _out239;
            _out239 = (this).GenType(_1872_toTpe, DCOMP.GenTypeContext.@default());
            _1886_rhsType = _out239;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1886_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1882_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out240;
          DCOMP._IOwnership _out241;
          (this).FromOwnership(r, _1883_recOwned, expectedOwnership, out _out240, out _out241);
          r = _out240;
          resultingOwnership = _out241;
        }
      } else {
        if ((_1881_nativeToType).is_Some) {
          DAST._IType _source106 = _1871_fromTpe;
          bool unmatched106 = true;
          if (unmatched106) {
            if (_source106.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source106.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1887_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1888_range0 = kind1.dtor_range;
                bool _1889_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1890_attributes0 = resolved1.dtor_attributes;
                unmatched106 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1891_nativeFromType;
                  _1891_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1888_range0);
                  if ((_1891_nativeFromType).is_Some) {
                    RAST._IExpr _1892_recursiveGen;
                    DCOMP._IOwnership _1893_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1894_recIdents;
                    RAST._IExpr _out242;
                    DCOMP._IOwnership _out243;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out244;
                    (this).GenExpr(_1870_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out242, out _out243, out _out244);
                    _1892_recursiveGen = _out242;
                    _1893_recOwned = _out243;
                    _1894_recIdents = _out244;
                    RAST._IExpr _out245;
                    DCOMP._IOwnership _out246;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1892_recursiveGen, (_1881_nativeToType).dtor_value), _1893_recOwned, expectedOwnership, out _out245, out _out246);
                    r = _out245;
                    resultingOwnership = _out246;
                    readIdents = _1894_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched106) {
            unmatched106 = false;
          }
          if (object.Equals(_1871_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1895_recursiveGen;
            DCOMP._IOwnership _1896_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1897_recIdents;
            RAST._IExpr _out247;
            DCOMP._IOwnership _out248;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
            (this).GenExpr(_1870_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out247, out _out248, out _out249);
            _1895_recursiveGen = _out247;
            _1896_recOwned = _out248;
            _1897_recIdents = _out249;
            RAST._IExpr _out250;
            DCOMP._IOwnership _out251;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1895_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1881_nativeToType).dtor_value), _1896_recOwned, expectedOwnership, out _out250, out _out251);
            r = _out250;
            resultingOwnership = _out251;
            readIdents = _1897_recIdents;
            return ;
          }
        }
        RAST._IExpr _out252;
        DCOMP._IOwnership _out253;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out254;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1870_expr, _1871_fromTpe, _1875_b), _1875_b, _1872_toTpe), selfIdent, env, expectedOwnership, out _out252, out _out253, out _out254);
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
      DAST._IExpression _1898_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _1899_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _1900_toTpe = _let_tmp_rhs61.dtor_typ;
      DAST._IType _let_tmp_rhs62 = _1899_fromTpe;
      DAST._IResolvedType _let_tmp_rhs63 = _let_tmp_rhs62.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1901___v124 = _let_tmp_rhs63.dtor_path;
      Dafny.ISequence<DAST._IType> _1902___v125 = _let_tmp_rhs63.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs64 = _let_tmp_rhs63.dtor_kind;
      DAST._IType _1903_b = _let_tmp_rhs64.dtor_baseType;
      DAST._INewtypeRange _1904_range = _let_tmp_rhs64.dtor_range;
      bool _1905_erase = _let_tmp_rhs64.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1906_attributes = _let_tmp_rhs63.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1907___v126 = _let_tmp_rhs63.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1908___v127 = _let_tmp_rhs63.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1909_nativeFromType;
      _1909_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1904_range);
      if (object.Equals(_1903_b, _1900_toTpe)) {
        RAST._IExpr _1910_recursiveGen;
        DCOMP._IOwnership _1911_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1912_recIdents;
        RAST._IExpr _out255;
        DCOMP._IOwnership _out256;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out257;
        (this).GenExpr(_1898_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out255, out _out256, out _out257);
        _1910_recursiveGen = _out255;
        _1911_recOwned = _out256;
        _1912_recIdents = _out257;
        readIdents = _1912_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source107 = _1909_nativeFromType;
        bool unmatched107 = true;
        if (unmatched107) {
          if (_source107.is_Some) {
            RAST._IType _1913_v = _source107.dtor_value;
            unmatched107 = false;
            RAST._IType _1914_toTpeRust;
            RAST._IType _out258;
            _out258 = (this).GenType(_1900_toTpe, DCOMP.GenTypeContext.@default());
            _1914_toTpeRust = _out258;
            r = ((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1914_toTpeRust))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1910_recursiveGen));
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            (this).FromOwned(r, expectedOwnership, out _out259, out _out260);
            r = _out259;
            resultingOwnership = _out260;
          }
        }
        if (unmatched107) {
          unmatched107 = false;
          if (_1905_erase) {
            r = _1910_recursiveGen;
          } else {
            r = (_1910_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out261;
          DCOMP._IOwnership _out262;
          (this).FromOwnership(r, _1911_recOwned, expectedOwnership, out _out261, out _out262);
          r = _out261;
          resultingOwnership = _out262;
        }
      } else {
        if ((_1909_nativeFromType).is_Some) {
          if (object.Equals(_1900_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1915_recursiveGen;
            DCOMP._IOwnership _1916_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1917_recIdents;
            RAST._IExpr _out263;
            DCOMP._IOwnership _out264;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out265;
            (this).GenExpr(_1898_expr, selfIdent, env, expectedOwnership, out _out263, out _out264, out _out265);
            _1915_recursiveGen = _out263;
            _1916_recOwned = _out264;
            _1917_recIdents = _out265;
            RAST._IExpr _out266;
            DCOMP._IOwnership _out267;
            (this).FromOwnership((((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(RAST.Expr.create_TypeAscription(_1915_recursiveGen, (this).DafnyCharUnderlying)), _1916_recOwned, expectedOwnership, out _out266, out _out267);
            r = _out266;
            resultingOwnership = _out267;
            readIdents = _1917_recIdents;
            return ;
          }
        }
        RAST._IExpr _out268;
        DCOMP._IOwnership _out269;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1898_expr, _1899_fromTpe, _1903_b), _1903_b, _1900_toTpe), selfIdent, env, expectedOwnership, out _out268, out _out269, out _out270);
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
        Std.Wrappers._IResult<__T, __E> _1918_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1918_valueOrError0).IsFailure()) {
          return (_1918_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1919_head = (_1918_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1920_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1920_valueOrError1).IsFailure()) {
            return (_1920_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1921_tail = (_1920_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1919_head), _1921_tail));
          }
        }
      }
    }
    public Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> UpcastConversionLambda(DAST._IType fromType, RAST._IType fromTpe, DAST._IType toType, RAST._IType toTpe, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> typeParams)
    {
      var _pat_let_tv195 = fromType;
      var _pat_let_tv196 = fromTpe;
      var _pat_let_tv197 = toType;
      var _pat_let_tv198 = toTpe;
      var _pat_let_tv199 = typeParams;
      if (object.Equals(fromTpe, toTpe)) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_id"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(fromTpe))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
      } else if (((fromTpe).IsObjectOrPointer()) && ((toTpe).IsObjectOrPointer())) {
        if (!(((toTpe).ObjectOrPointerUnderlying()).is_DynType)) {
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Failure(_System.Tuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>.create(fromType, fromTpe, toType, toTpe, typeParams));
        } else {
          RAST._IType _1922_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1923_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel((this).upcast)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1922_fromTpeUnderlying, _1923_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1924_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1924_valueOrError0).IsFailure()) {
          return (_1924_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1925_lambda = (_1924_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1925_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).AsExpr()).Apply1(_1925_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Dafny.ISequence<BigInteger> _1926_indices = ((((fromType).is_UserDefined) && ((((fromType).dtor_resolved).dtor_kind).is_Datatype)) ? (Std.Collections.Seq.__default.Filter<BigInteger>(Dafny.Helpers.Id<Func<RAST._IType, DAST._IType, Func<BigInteger, bool>>>((_1927_fromTpe, _1928_fromType) => ((System.Func<BigInteger, bool>)((_1929_i) => {
          return ((((_1929_i).Sign != -1) && ((_1929_i) < (new BigInteger(((_1927_fromTpe).dtor_arguments).Count)))) ? (!(((_1929_i).Sign != -1) && ((_1929_i) < (new BigInteger(((((_1928_fromType).dtor_resolved).dtor_kind).dtor_variances).Count)))) || (!((((((_1928_fromType).dtor_resolved).dtor_kind).dtor_variances).Select(_1929_i)).is_Nonvariant))) : (false));
        })))(fromTpe, fromType), ((System.Func<Dafny.ISequence<BigInteger>>) (() => {
          BigInteger dim14 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr14 = new BigInteger[Dafny.Helpers.ToIntChecked(dim14, "array size exceeds memory limit")];
          for (int i14 = 0; i14 < dim14; i14++) {
            var _1930_i = (BigInteger) i14;
            arr14[(int)(_1930_i)] = _1930_i;
          }
          return Dafny.Sequence<BigInteger>.FromArray(arr14);
        }))())) : (((System.Func<Dafny.ISequence<BigInteger>>) (() => {
          BigInteger dim15 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr15 = new BigInteger[Dafny.Helpers.ToIntChecked(dim15, "array size exceeds memory limit")];
          for (int i15 = 0; i15 < dim15; i15++) {
            var _1931_i = (BigInteger) i15;
            arr15[(int)(_1931_i)] = _1931_i;
          }
          return Dafny.Sequence<BigInteger>.FromArray(arr15);
        }))()));
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1932_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim16 = new BigInteger((_1926_indices).Count);
          var arr16 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim16, "array size exceeds memory limit")];
          for (int i16 = 0; i16 < dim16; i16++) {
            var _1933_j = (BigInteger) i16;
            arr16[(int)(_1933_j)] = Dafny.Helpers.Let<BigInteger, Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>((_1926_indices).Select(_1933_j), _pat_let28_0 => Dafny.Helpers.Let<BigInteger, Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>(_pat_let28_0, _1934_i => (this).UpcastConversionLambda((((_pat_let_tv195).dtor_resolved).dtor_typeArgs).Select(_1934_i), ((_pat_let_tv196).dtor_arguments).Select(_1934_i), (((_pat_let_tv197).dtor_resolved).dtor_typeArgs).Select(_1934_i), ((_pat_let_tv198).dtor_arguments).Select(_1934_i), _pat_let_tv199)));
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr16);
        }))());
        if ((_1932_valueOrError1).IsFailure()) {
          return (_1932_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1935_lambdas = (_1932_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim17 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr17 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim17, "array size exceeds memory limit")];
  for (int i17 = 0; i17 < dim17; i17++) {
    var _1936_i = (BigInteger) i17;
    arr17[(int)(_1936_i)] = ((fromTpe).dtor_arguments).Select(_1936_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr17);
}))())).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1935_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1937_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1938_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1939_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1940_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1941_valueOrError2 = (this).UpcastConversionLambda(_1939_newFromType, _1937_newFromTpe, _1940_newToType, _1938_newToTpe, typeParams);
        if ((_1941_valueOrError2).IsFailure()) {
          return (_1941_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1942_coerceArg = (_1941_valueOrError2).Extract();
          RAST._IPath _1943_collectionType = (RAST.__default.dafny__runtime).MSel(((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name);
          RAST._IExpr _1944_baseType = (((((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? (((_1943_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((((fromTpe).Expand()).dtor_arguments).Select(BigInteger.Zero), _1937_newFromTpe))) : (((_1943_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1937_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1944_baseType).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1942_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1945_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1945_valueOrError3).IsFailure()) {
          return (_1945_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1946_lambda = (_1945_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1946_lambda));
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
      DAST._IExpression _1947_expr = _let_tmp_rhs65.dtor_value;
      DAST._IType _1948_fromTpe = _let_tmp_rhs65.dtor_from;
      DAST._IType _1949_toTpe = _let_tmp_rhs65.dtor_typ;
      RAST._IType _1950_fromTpeGen;
      RAST._IType _out271;
      _out271 = (this).GenType(_1948_fromTpe, DCOMP.GenTypeContext.@default());
      _1950_fromTpeGen = _out271;
      RAST._IType _1951_toTpeGen;
      RAST._IType _out272;
      _out272 = (this).GenType(_1949_toTpe, DCOMP.GenTypeContext.@default());
      _1951_toTpeGen = _out272;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1952_upcastConverter;
      _1952_upcastConverter = (this).UpcastConversionLambda(_1948_fromTpe, _1950_fromTpeGen, _1949_toTpe, _1951_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1952_upcastConverter).is_Success) {
        RAST._IExpr _1953_conversionLambda;
        _1953_conversionLambda = (_1952_upcastConverter).dtor_value;
        RAST._IExpr _1954_recursiveGen;
        DCOMP._IOwnership _1955_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1956_recIdents;
        RAST._IExpr _out273;
        DCOMP._IOwnership _out274;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out275;
        (this).GenExpr(_1947_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out273, out _out274, out _out275);
        _1954_recursiveGen = _out273;
        _1955_recOwned = _out274;
        _1956_recIdents = _out275;
        readIdents = _1956_recIdents;
        r = (_1953_conversionLambda).Apply1(_1954_recursiveGen);
        RAST._IExpr _out276;
        DCOMP._IOwnership _out277;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out276, out _out277);
        r = _out276;
        resultingOwnership = _out277;
      } else if ((this).IsDowncastConversion(_1950_fromTpeGen, _1951_toTpeGen)) {
        RAST._IExpr _1957_recursiveGen;
        DCOMP._IOwnership _1958_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1959_recIdents;
        RAST._IExpr _out278;
        DCOMP._IOwnership _out279;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out280;
        (this).GenExpr(_1947_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out278, out _out279, out _out280);
        _1957_recursiveGen = _out278;
        _1958_recOwned = _out279;
        _1959_recIdents = _out280;
        readIdents = _1959_recIdents;
        _1951_toTpeGen = (_1951_toTpeGen).ObjectOrPointerUnderlying();
        r = (((RAST.__default.dafny__runtime).MSel((this).downcast)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1957_recursiveGen, RAST.Expr.create_ExprFromType(_1951_toTpeGen)));
        RAST._IExpr _out281;
        DCOMP._IOwnership _out282;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out281, out _out282);
        r = _out281;
        resultingOwnership = _out282;
      } else {
        RAST._IExpr _1960_recursiveGen;
        DCOMP._IOwnership _1961_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1962_recIdents;
        RAST._IExpr _out283;
        DCOMP._IOwnership _out284;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out285;
        (this).GenExpr(_1947_expr, selfIdent, env, expectedOwnership, out _out283, out _out284, out _out285);
        _1960_recursiveGen = _out283;
        _1961_recOwned = _out284;
        _1962_recIdents = _out285;
        readIdents = _1962_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs66 = _1952_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs67 = _let_tmp_rhs66.dtor_error;
        DAST._IType _1963_fromType = _let_tmp_rhs67.dtor__0;
        RAST._IType _1964_fromTpeGen = _let_tmp_rhs67.dtor__1;
        DAST._IType _1965_toType = _let_tmp_rhs67.dtor__2;
        RAST._IType _1966_toTpeGen = _let_tmp_rhs67.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1967_m = _let_tmp_rhs67.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1968_msg;
        _1968_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1964_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1966_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1968_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1960_recursiveGen)._ToString(DCOMP.__default.IND), _1968_msg));
        RAST._IExpr _out286;
        DCOMP._IOwnership _out287;
        (this).FromOwnership(r, _1961_recOwned, expectedOwnership, out _out286, out _out287);
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
      DAST._IExpression _1969_expr = _let_tmp_rhs68.dtor_value;
      DAST._IType _1970_fromTpe = _let_tmp_rhs68.dtor_from;
      DAST._IType _1971_toTpe = _let_tmp_rhs68.dtor_typ;
      if (object.Equals(_1970_fromTpe, _1971_toTpe)) {
        RAST._IExpr _1972_recursiveGen;
        DCOMP._IOwnership _1973_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1974_recIdents;
        RAST._IExpr _out288;
        DCOMP._IOwnership _out289;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
        (this).GenExpr(_1969_expr, selfIdent, env, expectedOwnership, out _out288, out _out289, out _out290);
        _1972_recursiveGen = _out288;
        _1973_recOwned = _out289;
        _1974_recIdents = _out290;
        r = _1972_recursiveGen;
        RAST._IExpr _out291;
        DCOMP._IOwnership _out292;
        (this).FromOwnership(r, _1973_recOwned, expectedOwnership, out _out291, out _out292);
        r = _out291;
        resultingOwnership = _out292;
        readIdents = _1974_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source108 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1970_fromTpe, _1971_toTpe);
        bool unmatched108 = true;
        if (unmatched108) {
          DAST._IType _10 = _source108.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1975_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1976_range = kind2.dtor_range;
              bool _1977_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1978_attributes = resolved2.dtor_attributes;
              unmatched108 = false;
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
        if (unmatched108) {
          DAST._IType _00 = _source108.dtor__0;
          if (_00.is_UserDefined) {
            DAST._IResolvedType resolved3 = _00.dtor_resolved;
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1979_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1980_range = kind3.dtor_range;
              bool _1981_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1982_attributes = resolved3.dtor_attributes;
              unmatched108 = false;
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
        if (unmatched108) {
          DAST._IType _01 = _source108.dtor__0;
          if (_01.is_Primitive) {
            DAST._IPrimitive _h72 = _01.dtor_Primitive_a0;
            if (_h72.is_Int) {
              DAST._IType _11 = _source108.dtor__1;
              if (_11.is_Primitive) {
                DAST._IPrimitive _h73 = _11.dtor_Primitive_a0;
                if (_h73.is_Real) {
                  unmatched108 = false;
                  {
                    RAST._IExpr _1983_recursiveGen;
                    DCOMP._IOwnership _1984___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1985_recIdents;
                    RAST._IExpr _out299;
                    DCOMP._IOwnership _out300;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out301;
                    (this).GenExpr(_1969_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out299, out _out300, out _out301);
                    _1983_recursiveGen = _out299;
                    _1984___v138 = _out300;
                    _1985_recIdents = _out301;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1983_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out302;
                    DCOMP._IOwnership _out303;
                    (this).FromOwned(r, expectedOwnership, out _out302, out _out303);
                    r = _out302;
                    resultingOwnership = _out303;
                    readIdents = _1985_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched108) {
          DAST._IType _02 = _source108.dtor__0;
          if (_02.is_Primitive) {
            DAST._IPrimitive _h74 = _02.dtor_Primitive_a0;
            if (_h74.is_Real) {
              DAST._IType _12 = _source108.dtor__1;
              if (_12.is_Primitive) {
                DAST._IPrimitive _h75 = _12.dtor_Primitive_a0;
                if (_h75.is_Int) {
                  unmatched108 = false;
                  {
                    RAST._IExpr _1986_recursiveGen;
                    DCOMP._IOwnership _1987___v139;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1988_recIdents;
                    RAST._IExpr _out304;
                    DCOMP._IOwnership _out305;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out306;
                    (this).GenExpr(_1969_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out304, out _out305, out _out306);
                    _1986_recursiveGen = _out304;
                    _1987___v139 = _out305;
                    _1988_recIdents = _out306;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1986_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out307;
                    DCOMP._IOwnership _out308;
                    (this).FromOwned(r, expectedOwnership, out _out307, out _out308);
                    r = _out307;
                    resultingOwnership = _out308;
                    readIdents = _1988_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched108) {
          DAST._IType _03 = _source108.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h76 = _03.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _13 = _source108.dtor__1;
              if (_13.is_Passthrough) {
                unmatched108 = false;
                {
                  RAST._IType _1989_rhsType;
                  RAST._IType _out309;
                  _out309 = (this).GenType(_1971_toTpe, DCOMP.GenTypeContext.@default());
                  _1989_rhsType = _out309;
                  RAST._IExpr _1990_recursiveGen;
                  DCOMP._IOwnership _1991___v141;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1992_recIdents;
                  RAST._IExpr _out310;
                  DCOMP._IOwnership _out311;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out312;
                  (this).GenExpr(_1969_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out310, out _out311, out _out312);
                  _1990_recursiveGen = _out310;
                  _1991___v141 = _out311;
                  _1992_recIdents = _out312;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1989_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1990_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out313;
                  DCOMP._IOwnership _out314;
                  (this).FromOwned(r, expectedOwnership, out _out313, out _out314);
                  r = _out313;
                  resultingOwnership = _out314;
                  readIdents = _1992_recIdents;
                }
              }
            }
          }
        }
        if (unmatched108) {
          DAST._IType _04 = _source108.dtor__0;
          if (_04.is_Passthrough) {
            DAST._IType _14 = _source108.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h77 = _14.dtor_Primitive_a0;
              if (_h77.is_Int) {
                unmatched108 = false;
                {
                  RAST._IType _1993_rhsType;
                  RAST._IType _out315;
                  _out315 = (this).GenType(_1970_fromTpe, DCOMP.GenTypeContext.@default());
                  _1993_rhsType = _out315;
                  RAST._IExpr _1994_recursiveGen;
                  DCOMP._IOwnership _1995___v143;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1996_recIdents;
                  RAST._IExpr _out316;
                  DCOMP._IOwnership _out317;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out318;
                  (this).GenExpr(_1969_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out316, out _out317, out _out318);
                  _1994_recursiveGen = _out316;
                  _1995___v143 = _out317;
                  _1996_recIdents = _out318;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1994_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out319;
                  DCOMP._IOwnership _out320;
                  (this).FromOwned(r, expectedOwnership, out _out319, out _out320);
                  r = _out319;
                  resultingOwnership = _out320;
                  readIdents = _1996_recIdents;
                }
              }
            }
          }
        }
        if (unmatched108) {
          DAST._IType _05 = _source108.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h78 = _05.dtor_Primitive_a0;
            if (_h78.is_Int) {
              DAST._IType _15 = _source108.dtor__1;
              if (_15.is_Primitive) {
                DAST._IPrimitive _h79 = _15.dtor_Primitive_a0;
                if (_h79.is_Char) {
                  unmatched108 = false;
                  {
                    RAST._IType _1997_rhsType;
                    RAST._IType _out321;
                    _out321 = (this).GenType(_1971_toTpe, DCOMP.GenTypeContext.@default());
                    _1997_rhsType = _out321;
                    RAST._IExpr _1998_recursiveGen;
                    DCOMP._IOwnership _1999___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2000_recIdents;
                    RAST._IExpr _out322;
                    DCOMP._IOwnership _out323;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out324;
                    (this).GenExpr(_1969_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out322, out _out323, out _out324);
                    _1998_recursiveGen = _out322;
                    _1999___v144 = _out323;
                    _2000_recIdents = _out324;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1998_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out325;
                    DCOMP._IOwnership _out326;
                    (this).FromOwned(r, expectedOwnership, out _out325, out _out326);
                    r = _out325;
                    resultingOwnership = _out326;
                    readIdents = _2000_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched108) {
          DAST._IType _06 = _source108.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h710 = _06.dtor_Primitive_a0;
            if (_h710.is_Char) {
              DAST._IType _16 = _source108.dtor__1;
              if (_16.is_Primitive) {
                DAST._IPrimitive _h711 = _16.dtor_Primitive_a0;
                if (_h711.is_Int) {
                  unmatched108 = false;
                  {
                    RAST._IType _2001_rhsType;
                    RAST._IType _out327;
                    _out327 = (this).GenType(_1970_fromTpe, DCOMP.GenTypeContext.@default());
                    _2001_rhsType = _out327;
                    RAST._IExpr _2002_recursiveGen;
                    DCOMP._IOwnership _2003___v145;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2004_recIdents;
                    RAST._IExpr _out328;
                    DCOMP._IOwnership _out329;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out330;
                    (this).GenExpr(_1969_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out328, out _out329, out _out330);
                    _2002_recursiveGen = _out328;
                    _2003___v145 = _out329;
                    _2004_recIdents = _out330;
                    r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1((_2002_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out331;
                    DCOMP._IOwnership _out332;
                    (this).FromOwned(r, expectedOwnership, out _out331, out _out332);
                    r = _out331;
                    resultingOwnership = _out332;
                    readIdents = _2004_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched108) {
          DAST._IType _07 = _source108.dtor__0;
          if (_07.is_Passthrough) {
            DAST._IType _17 = _source108.dtor__1;
            if (_17.is_Passthrough) {
              unmatched108 = false;
              {
                RAST._IExpr _2005_recursiveGen;
                DCOMP._IOwnership _2006___v148;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2007_recIdents;
                RAST._IExpr _out333;
                DCOMP._IOwnership _out334;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out335;
                (this).GenExpr(_1969_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out333, out _out334, out _out335);
                _2005_recursiveGen = _out333;
                _2006___v148 = _out334;
                _2007_recIdents = _out335;
                RAST._IType _2008_toTpeGen;
                RAST._IType _out336;
                _out336 = (this).GenType(_1971_toTpe, DCOMP.GenTypeContext.@default());
                _2008_toTpeGen = _out336;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_2005_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_2008_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out337;
                DCOMP._IOwnership _out338;
                (this).FromOwned(r, expectedOwnership, out _out337, out _out338);
                r = _out337;
                resultingOwnership = _out338;
                readIdents = _2007_recIdents;
              }
            }
          }
        }
        if (unmatched108) {
          unmatched108 = false;
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
      Std.Wrappers._IOption<RAST._IType> _2009_tpe;
      _2009_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _2010_placeboOpt;
      _2010_placeboOpt = (((_2009_tpe).is_Some) ? (((_2009_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _2011_currentlyBorrowed;
      _2011_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _2012_noNeedOfClone;
      _2012_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_2010_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _2011_currentlyBorrowed = false;
        _2012_noNeedOfClone = true;
        _2009_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_2010_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_2011_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_2009_tpe).is_Some) && (((_2009_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _2013_needObjectFromRef;
        _2013_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source109 = (selfIdent).dtor_dafnyType;
          bool unmatched109 = true;
          if (unmatched109) {
            if (_source109.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source109.dtor_resolved;
              DAST._IResolvedTypeBase _2014_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _2015_attributes = resolved4.dtor_attributes;
              unmatched109 = false;
              return ((_2014_base).is_Class) || ((_2014_base).is_Trait);
            }
          }
          if (unmatched109) {
            unmatched109 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_2013_needObjectFromRef) {
          r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_2012_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_2012_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_2011_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_2009_tpe).is_Some) && (((_2009_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_2016_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_2016_attributes).UniqueElements, false, (((_exists_var_3) => {
        DAST._IAttribute _2017_attribute = (DAST._IAttribute)_exists_var_3;
        return ((_2016_attributes).Contains(_2017_attribute)) && ((((_2017_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_2017_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      Dafny.ISequence<DAST._IFormal> _2018_signature;
      _2018_signature = (((name).is_CallName) ? ((((((name).dtor_receiverArg).is_Some) && ((name).dtor_receiverAsArgument)) ? (Dafny.Sequence<DAST._IFormal>.Concat(Dafny.Sequence<DAST._IFormal>.FromElements(((name).dtor_receiverArg).dtor_value), ((name).dtor_signature))) : (((name).dtor_signature)))) : (Dafny.Sequence<DAST._IFormal>.FromElements()));
      BigInteger _hi39 = new BigInteger((args).Count);
      for (BigInteger _2019_i = BigInteger.Zero; _2019_i < _hi39; _2019_i++) {
        DCOMP._IOwnership _2020_argOwnership;
        _2020_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if ((_2019_i) < (new BigInteger((_2018_signature).Count))) {
          RAST._IType _2021_tpe;
          RAST._IType _out342;
          _out342 = (this).GenType(((_2018_signature).Select(_2019_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _2021_tpe = _out342;
          if ((_2021_tpe).CanReadWithoutClone()) {
            _2020_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _2022_argExpr;
        DCOMP._IOwnership _2023___v155;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2024_argIdents;
        RAST._IExpr _out343;
        DCOMP._IOwnership _out344;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out345;
        (this).GenExpr((args).Select(_2019_i), selfIdent, env, _2020_argOwnership, out _out343, out _out344, out _out345);
        _2022_argExpr = _out343;
        _2023___v155 = _out344;
        _2024_argIdents = _out345;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2022_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2024_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi40 = new BigInteger((typeArgs).Count);
      for (BigInteger _2025_typeI = BigInteger.Zero; _2025_typeI < _hi40; _2025_typeI++) {
        RAST._IType _2026_typeExpr;
        RAST._IType _out346;
        _out346 = (this).GenType((typeArgs).Select(_2025_typeI), DCOMP.GenTypeContext.@default());
        _2026_typeExpr = _out346;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2026_typeExpr));
      }
      DAST._ICallName _source110 = name;
      bool unmatched110 = true;
      if (unmatched110) {
        if (_source110.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _2027_nameIdent = _source110.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType1 = _source110.dtor_onType;
          if (onType1.is_Some) {
            DAST._IType value10 = onType1.dtor_value;
            if (value10.is_UserDefined) {
              DAST._IResolvedType _2028_resolvedType = value10.dtor_resolved;
              unmatched110 = false;
              if ((((_2028_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_2029_resolvedType, _2030_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.SingleValue<Dafny.ISequence<Dafny.Rune>>(_2030_nameIdent), true, (((_forall_var_8) => {
                Dafny.ISequence<Dafny.Rune> _2031_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                return !(((_2029_resolvedType).dtor_properMethods).Contains(_2031_m)) || (!object.Equals(_2031_m, _2030_nameIdent));
              }))))(_2028_resolvedType, _2027_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_2028_resolvedType, (_2027_nameIdent)), _2028_resolvedType));
              } else {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
              }
            }
          }
        }
      }
      if (unmatched110) {
        unmatched110 = false;
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
      if ((((((fullNameQualifier).is_Some) && ((selfIdent).is_ThisTyped)) && (((selfIdent).dtor_dafnyType).is_UserDefined)) && ((this).IsSameResolvedType(((selfIdent).dtor_dafnyType).dtor_resolved, (fullNameQualifier).dtor_value))) && (!((this).HasExternAttributeRenamingModule(((fullNameQualifier).dtor_value).dtor_attributes)))) {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    }
    public Dafny.ISequence<Dafny.Rune> GetMethodName(DAST._IExpression @on, DAST._ICallName name)
    {
      var _pat_let_tv200 = @on;
      DAST._ICallName _source111 = name;
      bool unmatched111 = true;
      if (unmatched111) {
        if (_source111.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _2032_ident = _source111.dtor_name;
          unmatched111 = false;
          if ((_pat_let_tv200).is_ExternCompanion) {
            return (_2032_ident);
          } else {
            return DCOMP.__default.escapeName(_2032_ident);
          }
        }
      }
      if (unmatched111) {
        bool disjunctiveMatch15 = false;
        if (_source111.is_MapBuilderAdd) {
          disjunctiveMatch15 = true;
        }
        if (_source111.is_SetBuilderAdd) {
          disjunctiveMatch15 = true;
        }
        if (disjunctiveMatch15) {
          unmatched111 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
        }
      }
      if (unmatched111) {
        bool disjunctiveMatch16 = false;
        disjunctiveMatch16 = true;
        disjunctiveMatch16 = true;
        if (disjunctiveMatch16) {
          unmatched111 = false;
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
      DAST._IExpression _source112 = e;
      bool unmatched112 = true;
      if (unmatched112) {
        if (_source112.is_Literal) {
          unmatched112 = false;
          RAST._IExpr _out347;
          DCOMP._IOwnership _out348;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out347, out _out348, out _out349);
          r = _out347;
          resultingOwnership = _out348;
          readIdents = _out349;
        }
      }
      if (unmatched112) {
        if (_source112.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _2033_name = _source112.dtor_name;
          unmatched112 = false;
          {
            RAST._IExpr _out350;
            DCOMP._IOwnership _out351;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out352;
            (this).GenIdent(DCOMP.__default.escapeVar(_2033_name), selfIdent, env, expectedOwnership, out _out350, out _out351, out _out352);
            r = _out350;
            resultingOwnership = _out351;
            readIdents = _out352;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_ExternCompanion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2034_path = _source112.dtor_ExternCompanion_a0;
          unmatched112 = false;
          {
            RAST._IExpr _out353;
            _out353 = DCOMP.COMP.GenPathExpr(_2034_path, false);
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
      if (unmatched112) {
        if (_source112.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2035_path = _source112.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _2036_typeArgs = _source112.dtor_typeArgs;
          unmatched112 = false;
          {
            RAST._IExpr _out356;
            _out356 = DCOMP.COMP.GenPathExpr(_2035_path, true);
            r = _out356;
            if ((new BigInteger((_2036_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _2037_typeExprs;
              _2037_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi41 = new BigInteger((_2036_typeArgs).Count);
              for (BigInteger _2038_i = BigInteger.Zero; _2038_i < _hi41; _2038_i++) {
                RAST._IType _2039_typeExpr;
                RAST._IType _out357;
                _out357 = (this).GenType((_2036_typeArgs).Select(_2038_i), DCOMP.GenTypeContext.@default());
                _2039_typeExpr = _out357;
                _2037_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_2037_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2039_typeExpr));
              }
              r = (r).ApplyType(_2037_typeExprs);
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
      if (unmatched112) {
        if (_source112.is_InitializationValue) {
          DAST._IType _2040_typ = _source112.dtor_typ;
          unmatched112 = false;
          {
            RAST._IType _2041_typExpr;
            RAST._IType _out360;
            _out360 = (this).GenType(_2040_typ, DCOMP.GenTypeContext.@default());
            _2041_typExpr = _out360;
            if ((_2041_typExpr).IsObjectOrPointer()) {
              r = (_2041_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_2041_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
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
      if (unmatched112) {
        if (_source112.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _2042_values = _source112.dtor_Tuple_a0;
          unmatched112 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2043_exprs;
            _2043_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi42 = new BigInteger((_2042_values).Count);
            for (BigInteger _2044_i = BigInteger.Zero; _2044_i < _hi42; _2044_i++) {
              RAST._IExpr _2045_recursiveGen;
              DCOMP._IOwnership _2046___v165;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2047_recIdents;
              RAST._IExpr _out363;
              DCOMP._IOwnership _out364;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out365;
              (this).GenExpr((_2042_values).Select(_2044_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out363, out _out364, out _out365);
              _2045_recursiveGen = _out363;
              _2046___v165 = _out364;
              _2047_recIdents = _out365;
              _2043_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_2043_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2045_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2047_recIdents);
            }
            r = (((new BigInteger((_2042_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_2043_exprs)) : (RAST.__default.SystemTuple(_2043_exprs)));
            RAST._IExpr _out366;
            DCOMP._IOwnership _out367;
            (this).FromOwned(r, expectedOwnership, out _out366, out _out367);
            r = _out366;
            resultingOwnership = _out367;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2048_path = _source112.dtor_path;
          Dafny.ISequence<DAST._IType> _2049_typeArgs = _source112.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2050_args = _source112.dtor_args;
          unmatched112 = false;
          {
            RAST._IExpr _out368;
            _out368 = DCOMP.COMP.GenPathExpr(_2048_path, true);
            r = _out368;
            if ((new BigInteger((_2049_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _2051_typeExprs;
              _2051_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi43 = new BigInteger((_2049_typeArgs).Count);
              for (BigInteger _2052_i = BigInteger.Zero; _2052_i < _hi43; _2052_i++) {
                RAST._IType _2053_typeExpr;
                RAST._IType _out369;
                _out369 = (this).GenType((_2049_typeArgs).Select(_2052_i), DCOMP.GenTypeContext.@default());
                _2053_typeExpr = _out369;
                _2051_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_2051_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2053_typeExpr));
              }
              r = (r).ApplyType(_2051_typeExprs);
            }
            r = (r).FSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _2054_arguments;
            _2054_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi44 = new BigInteger((_2050_args).Count);
            for (BigInteger _2055_i = BigInteger.Zero; _2055_i < _hi44; _2055_i++) {
              RAST._IExpr _2056_recursiveGen;
              DCOMP._IOwnership _2057___v166;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2058_recIdents;
              RAST._IExpr _out370;
              DCOMP._IOwnership _out371;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out372;
              (this).GenExpr((_2050_args).Select(_2055_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out370, out _out371, out _out372);
              _2056_recursiveGen = _out370;
              _2057___v166 = _out371;
              _2058_recIdents = _out372;
              _2054_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2054_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2056_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2058_recIdents);
            }
            r = (r).Apply(_2054_arguments);
            RAST._IExpr _out373;
            DCOMP._IOwnership _out374;
            (this).FromOwned(r, expectedOwnership, out _out373, out _out374);
            r = _out373;
            resultingOwnership = _out374;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _2059_dims = _source112.dtor_dims;
          DAST._IType _2060_typ = _source112.dtor_typ;
          unmatched112 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_2059_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _2061_msg;
              _2061_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2061_msg);
              }
              r = RAST.Expr.create_RawExpr(_2061_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _2062_typeGen;
              RAST._IType _out375;
              _out375 = (this).GenType(_2060_typ, DCOMP.GenTypeContext.@default());
              _2062_typeGen = _out375;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _2063_dimExprs;
              _2063_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi45 = new BigInteger((_2059_dims).Count);
              for (BigInteger _2064_i = BigInteger.Zero; _2064_i < _hi45; _2064_i++) {
                RAST._IExpr _2065_recursiveGen;
                DCOMP._IOwnership _2066___v167;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2067_recIdents;
                RAST._IExpr _out376;
                DCOMP._IOwnership _out377;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out378;
                (this).GenExpr((_2059_dims).Select(_2064_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out376, out _out377, out _out378);
                _2065_recursiveGen = _out376;
                _2066___v167 = _out377;
                _2067_recIdents = _out378;
                _2063_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_2063_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_2065_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2067_recIdents);
              }
              if ((new BigInteger((_2059_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _2068_class__name;
                _2068_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_2059_dims).Count)));
                r = (((((RAST.__default.dafny__runtime).MSel(_2068_class__name)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2062_typeGen))).FSel((this).placebos__usize)).Apply(_2063_dimExprs);
              } else {
                r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2062_typeGen))).Apply(_2063_dimExprs);
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
      if (unmatched112) {
        if (_source112.is_ArrayIndexToInt) {
          DAST._IExpression _2069_underlying = _source112.dtor_value;
          unmatched112 = false;
          {
            RAST._IExpr _2070_recursiveGen;
            DCOMP._IOwnership _2071___v168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2072_recIdents;
            RAST._IExpr _out381;
            DCOMP._IOwnership _out382;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
            (this).GenExpr(_2069_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out381, out _out382, out _out383);
            _2070_recursiveGen = _out381;
            _2071___v168 = _out382;
            _2072_recIdents = _out383;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(_2070_recursiveGen);
            readIdents = _2072_recIdents;
            RAST._IExpr _out384;
            DCOMP._IOwnership _out385;
            (this).FromOwned(r, expectedOwnership, out _out384, out _out385);
            r = _out384;
            resultingOwnership = _out385;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_FinalizeNewArray) {
          DAST._IExpression _2073_underlying = _source112.dtor_value;
          DAST._IType _2074_typ = _source112.dtor_typ;
          unmatched112 = false;
          {
            RAST._IType _2075_tpe;
            RAST._IType _out386;
            _out386 = (this).GenType(_2074_typ, DCOMP.GenTypeContext.@default());
            _2075_tpe = _out386;
            RAST._IExpr _2076_recursiveGen;
            DCOMP._IOwnership _2077___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2078_recIdents;
            RAST._IExpr _out387;
            DCOMP._IOwnership _out388;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
            (this).GenExpr(_2073_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out387, out _out388, out _out389);
            _2076_recursiveGen = _out387;
            _2077___v169 = _out388;
            _2078_recIdents = _out389;
            readIdents = _2078_recIdents;
            if ((_2075_tpe).IsObjectOrPointer()) {
              RAST._IType _2079_t;
              _2079_t = (_2075_tpe).ObjectOrPointerUnderlying();
              if ((_2079_t).is_Array) {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).array__construct)).Apply1(_2076_recursiveGen);
              } else if ((_2079_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _2080_c;
                _2080_c = (_2079_t).MultiArrayClass();
                r = ((((RAST.__default.dafny__runtime).MSel(_2080_c)).AsExpr()).FSel((this).array__construct)).Apply1(_2076_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_2075_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_2075_tpe)._ToString(DCOMP.__default.IND)));
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
      if (unmatched112) {
        if (_source112.is_DatatypeValue) {
          DAST._IResolvedType _2081_datatypeType = _source112.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _2082_typeArgs = _source112.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _2083_variant = _source112.dtor_variant;
          bool _2084_isCo = _source112.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2085_values = _source112.dtor_contents;
          unmatched112 = false;
          {
            RAST._IExpr _out392;
            _out392 = DCOMP.COMP.GenPathExpr((_2081_datatypeType).dtor_path, true);
            r = _out392;
            Dafny.ISequence<RAST._IType> _2086_genTypeArgs;
            _2086_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi46 = new BigInteger((_2082_typeArgs).Count);
            for (BigInteger _2087_i = BigInteger.Zero; _2087_i < _hi46; _2087_i++) {
              RAST._IType _2088_typeExpr;
              RAST._IType _out393;
              _out393 = (this).GenType((_2082_typeArgs).Select(_2087_i), DCOMP.GenTypeContext.@default());
              _2088_typeExpr = _out393;
              _2086_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_2086_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_2088_typeExpr));
            }
            if ((new BigInteger((_2082_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_2086_genTypeArgs);
            }
            r = (r).FSel(DCOMP.__default.escapeName(_2083_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _2089_assignments;
            _2089_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi47 = new BigInteger((_2085_values).Count);
            for (BigInteger _2090_i = BigInteger.Zero; _2090_i < _hi47; _2090_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs69 = (_2085_values).Select(_2090_i);
              Dafny.ISequence<Dafny.Rune> _2091_name = _let_tmp_rhs69.dtor__0;
              DAST._IExpression _2092_value = _let_tmp_rhs69.dtor__1;
              if (_2084_isCo) {
                RAST._IExpr _2093_recursiveGen;
                DCOMP._IOwnership _2094___v170;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2095_recIdents;
                RAST._IExpr _out394;
                DCOMP._IOwnership _out395;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out396;
                (this).GenExpr(_2092_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out394, out _out395, out _out396);
                _2093_recursiveGen = _out394;
                _2094___v170 = _out395;
                _2095_recIdents = _out396;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2095_recIdents);
                Dafny.ISequence<Dafny.Rune> _2096_allReadCloned;
                _2096_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_2095_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _2097_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2095_recIdents).Elements) {
                    _2097_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                    if ((_2095_recIdents).Contains(_2097_next)) {
                      goto after__ASSIGN_SUCH_THAT_3;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4811)");
                after__ASSIGN_SUCH_THAT_3: ;
                  _2096_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2096_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _2097_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2097_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _2095_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2095_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2097_next));
                }
                Dafny.ISequence<Dafny.Rune> _2098_wasAssigned;
                _2098_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _2096_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_2093_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _2089_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2089_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_2091_name), RAST.Expr.create_RawExpr(_2098_wasAssigned))));
              } else {
                RAST._IExpr _2099_recursiveGen;
                DCOMP._IOwnership _2100___v171;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2101_recIdents;
                RAST._IExpr _out397;
                DCOMP._IOwnership _out398;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
                (this).GenExpr(_2092_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out397, out _out398, out _out399);
                _2099_recursiveGen = _out397;
                _2100___v171 = _out398;
                _2101_recIdents = _out399;
                _2089_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2089_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_2091_name), _2099_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2101_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _2089_assignments);
            if ((this).IsRcWrapped((_2081_datatypeType).dtor_attributes)) {
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
      if (unmatched112) {
        if (_source112.is_Convert) {
          unmatched112 = false;
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
      if (unmatched112) {
        if (_source112.is_SeqConstruct) {
          DAST._IExpression _2102_length = _source112.dtor_length;
          DAST._IExpression _2103_expr = _source112.dtor_elem;
          unmatched112 = false;
          {
            RAST._IExpr _2104_recursiveGen;
            DCOMP._IOwnership _2105___v175;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2106_recIdents;
            RAST._IExpr _out405;
            DCOMP._IOwnership _out406;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out407;
            (this).GenExpr(_2103_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out405, out _out406, out _out407);
            _2104_recursiveGen = _out405;
            _2105___v175 = _out406;
            _2106_recIdents = _out407;
            RAST._IExpr _2107_lengthGen;
            DCOMP._IOwnership _2108___v176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2109_lengthIdents;
            RAST._IExpr _out408;
            DCOMP._IOwnership _out409;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out410;
            (this).GenExpr(_2102_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out408, out _out409, out _out410);
            _2107_lengthGen = _out408;
            _2108___v176 = _out409;
            _2109_lengthIdents = _out410;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_2104_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_2107_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2106_recIdents, _2109_lengthIdents);
            RAST._IExpr _out411;
            DCOMP._IOwnership _out412;
            (this).FromOwned(r, expectedOwnership, out _out411, out _out412);
            r = _out411;
            resultingOwnership = _out412;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _2110_exprs = _source112.dtor_elements;
          DAST._IType _2111_typ = _source112.dtor_typ;
          unmatched112 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _2112_genTpe;
            RAST._IType _out413;
            _out413 = (this).GenType(_2111_typ, DCOMP.GenTypeContext.@default());
            _2112_genTpe = _out413;
            BigInteger _2113_i;
            _2113_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2114_args;
            _2114_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2113_i) < (new BigInteger((_2110_exprs).Count))) {
              RAST._IExpr _2115_recursiveGen;
              DCOMP._IOwnership _2116___v177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2117_recIdents;
              RAST._IExpr _out414;
              DCOMP._IOwnership _out415;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out416;
              (this).GenExpr((_2110_exprs).Select(_2113_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out414, out _out415, out _out416);
              _2115_recursiveGen = _out414;
              _2116___v177 = _out415;
              _2117_recIdents = _out416;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2117_recIdents);
              _2114_args = Dafny.Sequence<RAST._IExpr>.Concat(_2114_args, Dafny.Sequence<RAST._IExpr>.FromElements(_2115_recursiveGen));
              _2113_i = (_2113_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).AsExpr()).Apply(_2114_args);
            if ((new BigInteger((_2114_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType()).Apply1(_2112_genTpe));
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
      if (unmatched112) {
        if (_source112.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _2118_exprs = _source112.dtor_elements;
          unmatched112 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2119_generatedValues;
            _2119_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2120_i;
            _2120_i = BigInteger.Zero;
            while ((_2120_i) < (new BigInteger((_2118_exprs).Count))) {
              RAST._IExpr _2121_recursiveGen;
              DCOMP._IOwnership _2122___v178;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2123_recIdents;
              RAST._IExpr _out419;
              DCOMP._IOwnership _out420;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out421;
              (this).GenExpr((_2118_exprs).Select(_2120_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out419, out _out420, out _out421);
              _2121_recursiveGen = _out419;
              _2122___v178 = _out420;
              _2123_recIdents = _out421;
              _2119_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2119_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2121_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2123_recIdents);
              _2120_i = (_2120_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).AsExpr()).Apply(_2119_generatedValues);
            RAST._IExpr _out422;
            DCOMP._IOwnership _out423;
            (this).FromOwned(r, expectedOwnership, out _out422, out _out423);
            r = _out422;
            resultingOwnership = _out423;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _2124_exprs = _source112.dtor_elements;
          unmatched112 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2125_generatedValues;
            _2125_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2126_i;
            _2126_i = BigInteger.Zero;
            while ((_2126_i) < (new BigInteger((_2124_exprs).Count))) {
              RAST._IExpr _2127_recursiveGen;
              DCOMP._IOwnership _2128___v179;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2129_recIdents;
              RAST._IExpr _out424;
              DCOMP._IOwnership _out425;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out426;
              (this).GenExpr((_2124_exprs).Select(_2126_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out424, out _out425, out _out426);
              _2127_recursiveGen = _out424;
              _2128___v179 = _out425;
              _2129_recIdents = _out426;
              _2125_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2125_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2127_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2129_recIdents);
              _2126_i = (_2126_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).AsExpr()).Apply(_2125_generatedValues);
            RAST._IExpr _out427;
            DCOMP._IOwnership _out428;
            (this).FromOwned(r, expectedOwnership, out _out427, out _out428);
            r = _out427;
            resultingOwnership = _out428;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_ToMultiset) {
          DAST._IExpression _2130_expr = _source112.dtor_ToMultiset_a0;
          unmatched112 = false;
          {
            RAST._IExpr _2131_recursiveGen;
            DCOMP._IOwnership _2132___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2133_recIdents;
            RAST._IExpr _out429;
            DCOMP._IOwnership _out430;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out431;
            (this).GenExpr(_2130_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out429, out _out430, out _out431);
            _2131_recursiveGen = _out429;
            _2132___v180 = _out430;
            _2133_recIdents = _out431;
            r = ((_2131_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2133_recIdents;
            RAST._IExpr _out432;
            DCOMP._IOwnership _out433;
            (this).FromOwned(r, expectedOwnership, out _out432, out _out433);
            r = _out432;
            resultingOwnership = _out433;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2134_mapElems = _source112.dtor_mapElems;
          unmatched112 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _2135_generatedValues;
            _2135_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2136_i;
            _2136_i = BigInteger.Zero;
            while ((_2136_i) < (new BigInteger((_2134_mapElems).Count))) {
              RAST._IExpr _2137_recursiveGenKey;
              DCOMP._IOwnership _2138___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2139_recIdentsKey;
              RAST._IExpr _out434;
              DCOMP._IOwnership _out435;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
              (this).GenExpr(((_2134_mapElems).Select(_2136_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out434, out _out435, out _out436);
              _2137_recursiveGenKey = _out434;
              _2138___v181 = _out435;
              _2139_recIdentsKey = _out436;
              RAST._IExpr _2140_recursiveGenValue;
              DCOMP._IOwnership _2141___v182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2142_recIdentsValue;
              RAST._IExpr _out437;
              DCOMP._IOwnership _out438;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
              (this).GenExpr(((_2134_mapElems).Select(_2136_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out437, out _out438, out _out439);
              _2140_recursiveGenValue = _out437;
              _2141___v182 = _out438;
              _2142_recIdentsValue = _out439;
              _2135_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_2135_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_2137_recursiveGenKey, _2140_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2139_recIdentsKey), _2142_recIdentsValue);
              _2136_i = (_2136_i) + (BigInteger.One);
            }
            _2136_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2143_arguments;
            _2143_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2136_i) < (new BigInteger((_2135_generatedValues).Count))) {
              RAST._IExpr _2144_genKey;
              _2144_genKey = ((_2135_generatedValues).Select(_2136_i)).dtor__0;
              RAST._IExpr _2145_genValue;
              _2145_genValue = ((_2135_generatedValues).Select(_2136_i)).dtor__1;
              _2143_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2143_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _2144_genKey, _2145_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _2136_i = (_2136_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).AsExpr()).Apply(_2143_arguments);
            RAST._IExpr _out440;
            DCOMP._IOwnership _out441;
            (this).FromOwned(r, expectedOwnership, out _out440, out _out441);
            r = _out440;
            resultingOwnership = _out441;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_SeqUpdate) {
          DAST._IExpression _2146_expr = _source112.dtor_expr;
          DAST._IExpression _2147_index = _source112.dtor_indexExpr;
          DAST._IExpression _2148_value = _source112.dtor_value;
          unmatched112 = false;
          {
            RAST._IExpr _2149_exprR;
            DCOMP._IOwnership _2150___v183;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2151_exprIdents;
            RAST._IExpr _out442;
            DCOMP._IOwnership _out443;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out444;
            (this).GenExpr(_2146_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out442, out _out443, out _out444);
            _2149_exprR = _out442;
            _2150___v183 = _out443;
            _2151_exprIdents = _out444;
            RAST._IExpr _2152_indexR;
            DCOMP._IOwnership _2153_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2154_indexIdents;
            RAST._IExpr _out445;
            DCOMP._IOwnership _out446;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
            (this).GenExpr(_2147_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out445, out _out446, out _out447);
            _2152_indexR = _out445;
            _2153_indexOwnership = _out446;
            _2154_indexIdents = _out447;
            RAST._IExpr _2155_valueR;
            DCOMP._IOwnership _2156_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2157_valueIdents;
            RAST._IExpr _out448;
            DCOMP._IOwnership _out449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out450;
            (this).GenExpr(_2148_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out448, out _out449, out _out450);
            _2155_valueR = _out448;
            _2156_valueOwnership = _out449;
            _2157_valueIdents = _out450;
            r = ((_2149_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2152_indexR, _2155_valueR));
            RAST._IExpr _out451;
            DCOMP._IOwnership _out452;
            (this).FromOwned(r, expectedOwnership, out _out451, out _out452);
            r = _out451;
            resultingOwnership = _out452;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2151_exprIdents, _2154_indexIdents), _2157_valueIdents);
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_MapUpdate) {
          DAST._IExpression _2158_expr = _source112.dtor_expr;
          DAST._IExpression _2159_index = _source112.dtor_indexExpr;
          DAST._IExpression _2160_value = _source112.dtor_value;
          unmatched112 = false;
          {
            RAST._IExpr _2161_exprR;
            DCOMP._IOwnership _2162___v184;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2163_exprIdents;
            RAST._IExpr _out453;
            DCOMP._IOwnership _out454;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out455;
            (this).GenExpr(_2158_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out453, out _out454, out _out455);
            _2161_exprR = _out453;
            _2162___v184 = _out454;
            _2163_exprIdents = _out455;
            RAST._IExpr _2164_indexR;
            DCOMP._IOwnership _2165_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2166_indexIdents;
            RAST._IExpr _out456;
            DCOMP._IOwnership _out457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out458;
            (this).GenExpr(_2159_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out456, out _out457, out _out458);
            _2164_indexR = _out456;
            _2165_indexOwnership = _out457;
            _2166_indexIdents = _out458;
            RAST._IExpr _2167_valueR;
            DCOMP._IOwnership _2168_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2169_valueIdents;
            RAST._IExpr _out459;
            DCOMP._IOwnership _out460;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out461;
            (this).GenExpr(_2160_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out459, out _out460, out _out461);
            _2167_valueR = _out459;
            _2168_valueOwnership = _out460;
            _2169_valueIdents = _out461;
            r = ((_2161_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2164_indexR, _2167_valueR));
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            (this).FromOwned(r, expectedOwnership, out _out462, out _out463);
            r = _out462;
            resultingOwnership = _out463;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2163_exprIdents, _2166_indexIdents), _2169_valueIdents);
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_This) {
          unmatched112 = false;
          {
            DCOMP._ISelfInfo _source113 = selfIdent;
            bool unmatched113 = true;
            if (unmatched113) {
              if (_source113.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _2170_id = _source113.dtor_rSelfName;
                DAST._IType _2171_dafnyType = _source113.dtor_dafnyType;
                unmatched113 = false;
                {
                  RAST._IExpr _out464;
                  DCOMP._IOwnership _out465;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
                  (this).GenIdent(_2170_id, selfIdent, env, expectedOwnership, out _out464, out _out465, out _out466);
                  r = _out464;
                  resultingOwnership = _out465;
                  readIdents = _out466;
                }
              }
            }
            if (unmatched113) {
              DCOMP._ISelfInfo _2172_None = _source113;
              unmatched113 = false;
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
      if (unmatched112) {
        if (_source112.is_Ite) {
          DAST._IExpression _2173_cond = _source112.dtor_cond;
          DAST._IExpression _2174_t = _source112.dtor_thn;
          DAST._IExpression _2175_f = _source112.dtor_els;
          unmatched112 = false;
          {
            RAST._IExpr _2176_cond;
            DCOMP._IOwnership _2177___v185;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2178_recIdentsCond;
            RAST._IExpr _out469;
            DCOMP._IOwnership _out470;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out471;
            (this).GenExpr(_2173_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out469, out _out470, out _out471);
            _2176_cond = _out469;
            _2177___v185 = _out470;
            _2178_recIdentsCond = _out471;
            RAST._IExpr _2179_fExpr;
            DCOMP._IOwnership _2180_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2181_recIdentsF;
            RAST._IExpr _out472;
            DCOMP._IOwnership _out473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
            (this).GenExpr(_2175_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out472, out _out473, out _out474);
            _2179_fExpr = _out472;
            _2180_fOwned = _out473;
            _2181_recIdentsF = _out474;
            RAST._IExpr _2182_tExpr;
            DCOMP._IOwnership _2183___v186;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2184_recIdentsT;
            RAST._IExpr _out475;
            DCOMP._IOwnership _out476;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out477;
            (this).GenExpr(_2174_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out475, out _out476, out _out477);
            _2182_tExpr = _out475;
            _2183___v186 = _out476;
            _2184_recIdentsT = _out477;
            r = RAST.Expr.create_IfExpr(_2176_cond, _2182_tExpr, _2179_fExpr);
            RAST._IExpr _out478;
            DCOMP._IOwnership _out479;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out478, out _out479);
            r = _out478;
            resultingOwnership = _out479;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2178_recIdentsCond, _2184_recIdentsT), _2181_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source112.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _2185_e = _source112.dtor_expr;
            DAST.Format._IUnaryOpFormat _2186_format = _source112.dtor_format1;
            unmatched112 = false;
            {
              RAST._IExpr _2187_recursiveGen;
              DCOMP._IOwnership _2188___v187;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2189_recIdents;
              RAST._IExpr _out480;
              DCOMP._IOwnership _out481;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out482;
              (this).GenExpr(_2185_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out480, out _out481, out _out482);
              _2187_recursiveGen = _out480;
              _2188___v187 = _out481;
              _2189_recIdents = _out482;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _2187_recursiveGen, _2186_format);
              RAST._IExpr _out483;
              DCOMP._IOwnership _out484;
              (this).FromOwned(r, expectedOwnership, out _out483, out _out484);
              r = _out483;
              resultingOwnership = _out484;
              readIdents = _2189_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source112.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _2190_e = _source112.dtor_expr;
            DAST.Format._IUnaryOpFormat _2191_format = _source112.dtor_format1;
            unmatched112 = false;
            {
              RAST._IExpr _2192_recursiveGen;
              DCOMP._IOwnership _2193___v188;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2194_recIdents;
              RAST._IExpr _out485;
              DCOMP._IOwnership _out486;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out487;
              (this).GenExpr(_2190_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out485, out _out486, out _out487);
              _2192_recursiveGen = _out485;
              _2193___v188 = _out486;
              _2194_recIdents = _out487;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _2192_recursiveGen, _2191_format);
              RAST._IExpr _out488;
              DCOMP._IOwnership _out489;
              (this).FromOwned(r, expectedOwnership, out _out488, out _out489);
              r = _out488;
              resultingOwnership = _out489;
              readIdents = _2194_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source112.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _2195_e = _source112.dtor_expr;
            DAST.Format._IUnaryOpFormat _2196_format = _source112.dtor_format1;
            unmatched112 = false;
            {
              RAST._IExpr _2197_recursiveGen;
              DCOMP._IOwnership _2198_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2199_recIdents;
              RAST._IExpr _out490;
              DCOMP._IOwnership _out491;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out492;
              (this).GenExpr(_2195_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out490, out _out491, out _out492);
              _2197_recursiveGen = _out490;
              _2198_recOwned = _out491;
              _2199_recIdents = _out492;
              r = ((_2197_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out493;
              DCOMP._IOwnership _out494;
              (this).FromOwned(r, expectedOwnership, out _out493, out _out494);
              r = _out493;
              resultingOwnership = _out494;
              readIdents = _2199_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_BinOp) {
          unmatched112 = false;
          RAST._IExpr _out495;
          DCOMP._IOwnership _out496;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out497;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out495, out _out496, out _out497);
          r = _out495;
          resultingOwnership = _out496;
          readIdents = _out497;
        }
      }
      if (unmatched112) {
        if (_source112.is_ArrayLen) {
          DAST._IExpression _2200_expr = _source112.dtor_expr;
          DAST._IType _2201_exprType = _source112.dtor_exprType;
          BigInteger _2202_dim = _source112.dtor_dim;
          bool _2203_native = _source112.dtor_native;
          unmatched112 = false;
          {
            RAST._IExpr _2204_recursiveGen;
            DCOMP._IOwnership _2205___v193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2206_recIdents;
            RAST._IExpr _out498;
            DCOMP._IOwnership _out499;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
            (this).GenExpr(_2200_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out498, out _out499, out _out500);
            _2204_recursiveGen = _out498;
            _2205___v193 = _out499;
            _2206_recIdents = _out500;
            RAST._IType _2207_arrayType;
            RAST._IType _out501;
            _out501 = (this).GenType(_2201_exprType, DCOMP.GenTypeContext.@default());
            _2207_arrayType = _out501;
            if (!((_2207_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2208_msg;
              _2208_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2207_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2208_msg);
              r = RAST.Expr.create_RawExpr(_2208_msg);
            } else {
              RAST._IType _2209_underlying;
              _2209_underlying = (_2207_arrayType).ObjectOrPointerUnderlying();
              if (((_2202_dim).Sign == 0) && ((_2209_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2204_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2202_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2204_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_2204_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_2202_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_2203_native)) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(r);
              }
            }
            RAST._IExpr _out502;
            DCOMP._IOwnership _out503;
            (this).FromOwned(r, expectedOwnership, out _out502, out _out503);
            r = _out502;
            resultingOwnership = _out503;
            readIdents = _2206_recIdents;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_MapKeys) {
          DAST._IExpression _2210_expr = _source112.dtor_expr;
          unmatched112 = false;
          {
            RAST._IExpr _2211_recursiveGen;
            DCOMP._IOwnership _2212___v194;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2213_recIdents;
            RAST._IExpr _out504;
            DCOMP._IOwnership _out505;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out506;
            (this).GenExpr(_2210_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out504, out _out505, out _out506);
            _2211_recursiveGen = _out504;
            _2212___v194 = _out505;
            _2213_recIdents = _out506;
            readIdents = _2213_recIdents;
            r = ((_2211_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out507;
            DCOMP._IOwnership _out508;
            (this).FromOwned(r, expectedOwnership, out _out507, out _out508);
            r = _out507;
            resultingOwnership = _out508;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_MapValues) {
          DAST._IExpression _2214_expr = _source112.dtor_expr;
          unmatched112 = false;
          {
            RAST._IExpr _2215_recursiveGen;
            DCOMP._IOwnership _2216___v195;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2217_recIdents;
            RAST._IExpr _out509;
            DCOMP._IOwnership _out510;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out511;
            (this).GenExpr(_2214_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out509, out _out510, out _out511);
            _2215_recursiveGen = _out509;
            _2216___v195 = _out510;
            _2217_recIdents = _out511;
            readIdents = _2217_recIdents;
            r = ((_2215_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out512;
            DCOMP._IOwnership _out513;
            (this).FromOwned(r, expectedOwnership, out _out512, out _out513);
            r = _out512;
            resultingOwnership = _out513;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_MapItems) {
          DAST._IExpression _2218_expr = _source112.dtor_expr;
          unmatched112 = false;
          {
            RAST._IExpr _2219_recursiveGen;
            DCOMP._IOwnership _2220___v196;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2221_recIdents;
            RAST._IExpr _out514;
            DCOMP._IOwnership _out515;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out516;
            (this).GenExpr(_2218_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out514, out _out515, out _out516);
            _2219_recursiveGen = _out514;
            _2220___v196 = _out515;
            _2221_recIdents = _out516;
            readIdents = _2221_recIdents;
            r = ((_2219_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("items"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out517;
            DCOMP._IOwnership _out518;
            (this).FromOwned(r, expectedOwnership, out _out517, out _out518);
            r = _out517;
            resultingOwnership = _out518;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_SelectFn) {
          DAST._IExpression _2222_on = _source112.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2223_field = _source112.dtor_field;
          bool _2224_isDatatype = _source112.dtor_onDatatype;
          bool _2225_isStatic = _source112.dtor_isStatic;
          bool _2226_isConstant = _source112.dtor_isConstant;
          Dafny.ISequence<DAST._IType> _2227_arguments = _source112.dtor_arguments;
          unmatched112 = false;
          {
            RAST._IExpr _2228_onExpr;
            DCOMP._IOwnership _2229_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2230_recIdents;
            RAST._IExpr _out519;
            DCOMP._IOwnership _out520;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
            (this).GenExpr(_2222_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out519, out _out520, out _out521);
            _2228_onExpr = _out519;
            _2229_onOwned = _out520;
            _2230_recIdents = _out521;
            Dafny.ISequence<Dafny.Rune> _2231_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2232_onString;
            _2232_onString = (_2228_onExpr)._ToString(DCOMP.__default.IND);
            if (_2225_isStatic) {
              DCOMP._IEnvironment _2233_lEnv;
              _2233_lEnv = env;
              Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>> _2234_args;
              _2234_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements();
              _2231_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|");
              BigInteger _hi48 = new BigInteger((_2227_arguments).Count);
              for (BigInteger _2235_i = BigInteger.Zero; _2235_i < _hi48; _2235_i++) {
                if ((_2235_i).Sign == 1) {
                  _2231_s = Dafny.Sequence<Dafny.Rune>.Concat(_2231_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                RAST._IType _2236_ty;
                RAST._IType _out522;
                _out522 = (this).GenType((_2227_arguments).Select(_2235_i), DCOMP.GenTypeContext.@default());
                _2236_ty = _out522;
                RAST._IType _2237_bTy;
                _2237_bTy = RAST.Type.create_Borrowed(_2236_ty);
                Dafny.ISequence<Dafny.Rune> _2238_name;
                _2238_name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), Std.Strings.__default.OfInt(_2235_i));
                _2233_lEnv = (_2233_lEnv).AddAssigned(_2238_name, _2237_bTy);
                _2234_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.Concat(_2234_args, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>.create(_2238_name, _2236_ty)));
                _2231_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2231_s, _2238_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_2237_bTy)._ToString(DCOMP.__default.IND));
              }
              _2231_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2231_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| ")), _2232_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeVar(_2223_field)), ((_2226_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("));
              BigInteger _hi49 = new BigInteger((_2234_args).Count);
              for (BigInteger _2239_i = BigInteger.Zero; _2239_i < _hi49; _2239_i++) {
                if ((_2239_i).Sign == 1) {
                  _2231_s = Dafny.Sequence<Dafny.Rune>.Concat(_2231_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType> _let_tmp_rhs70 = (_2234_args).Select(_2239_i);
                Dafny.ISequence<Dafny.Rune> _2240_name = _let_tmp_rhs70.dtor__0;
                RAST._IType _2241_ty = _let_tmp_rhs70.dtor__1;
                RAST._IExpr _2242_rIdent;
                DCOMP._IOwnership _2243___v197;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2244___v198;
                RAST._IExpr _out523;
                DCOMP._IOwnership _out524;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
                (this).GenIdent(_2240_name, selfIdent, _2233_lEnv, (((_2241_ty).CanReadWithoutClone()) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed())), out _out523, out _out524, out _out525);
                _2242_rIdent = _out523;
                _2243___v197 = _out524;
                _2244___v198 = _out525;
                _2231_s = Dafny.Sequence<Dafny.Rune>.Concat(_2231_s, (_2242_rIdent)._ToString(DCOMP.__default.IND));
              }
              _2231_s = Dafny.Sequence<Dafny.Rune>.Concat(_2231_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            } else {
              _2231_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2231_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2231_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2232_onString), ((object.Equals(_2229_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2245_args;
              _2245_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2246_i;
              _2246_i = BigInteger.Zero;
              while ((_2246_i) < (new BigInteger((_2227_arguments).Count))) {
                if ((_2246_i).Sign == 1) {
                  _2245_args = Dafny.Sequence<Dafny.Rune>.Concat(_2245_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2245_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2245_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2246_i));
                _2246_i = (_2246_i) + (BigInteger.One);
              }
              _2231_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2231_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2245_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2231_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2231_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeVar(_2223_field)), ((_2226_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2245_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2231_s = Dafny.Sequence<Dafny.Rune>.Concat(_2231_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2231_s = Dafny.Sequence<Dafny.Rune>.Concat(_2231_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2247_typeShape;
            _2247_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2248_i;
            _2248_i = BigInteger.Zero;
            while ((_2248_i) < (new BigInteger((_2227_arguments).Count))) {
              if ((_2248_i).Sign == 1) {
                _2247_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2247_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2247_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2247_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2248_i = (_2248_i) + (BigInteger.One);
            }
            _2247_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2247_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2231_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2231_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2247_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2231_s);
            RAST._IExpr _out526;
            DCOMP._IOwnership _out527;
            (this).FromOwned(r, expectedOwnership, out _out526, out _out527);
            r = _out526;
            resultingOwnership = _out527;
            readIdents = _2230_recIdents;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_Select) {
          DAST._IExpression _2249_on = _source112.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2250_field = _source112.dtor_field;
          bool _2251_isConstant = _source112.dtor_isConstant;
          bool _2252_isDatatype = _source112.dtor_onDatatype;
          DAST._IType _2253_fieldType = _source112.dtor_fieldType;
          unmatched112 = false;
          {
            if (((_2249_on).is_Companion) || ((_2249_on).is_ExternCompanion)) {
              RAST._IExpr _2254_onExpr;
              DCOMP._IOwnership _2255_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2256_recIdents;
              RAST._IExpr _out528;
              DCOMP._IOwnership _out529;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
              (this).GenExpr(_2249_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out528, out _out529, out _out530);
              _2254_onExpr = _out528;
              _2255_onOwned = _out529;
              _2256_recIdents = _out530;
              r = ((_2254_onExpr).FSel(DCOMP.__default.escapeVar(_2250_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out531;
              DCOMP._IOwnership _out532;
              (this).FromOwned(r, expectedOwnership, out _out531, out _out532);
              r = _out531;
              resultingOwnership = _out532;
              readIdents = _2256_recIdents;
              return ;
            } else if (_2252_isDatatype) {
              RAST._IExpr _2257_onExpr;
              DCOMP._IOwnership _2258_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2259_recIdents;
              RAST._IExpr _out533;
              DCOMP._IOwnership _out534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
              (this).GenExpr(_2249_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out533, out _out534, out _out535);
              _2257_onExpr = _out533;
              _2258_onOwned = _out534;
              _2259_recIdents = _out535;
              r = ((_2257_onExpr).Sel(DCOMP.__default.escapeVar(_2250_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2260_typ;
              RAST._IType _out536;
              _out536 = (this).GenType(_2253_fieldType, DCOMP.GenTypeContext.@default());
              _2260_typ = _out536;
              RAST._IExpr _out537;
              DCOMP._IOwnership _out538;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out537, out _out538);
              r = _out537;
              resultingOwnership = _out538;
              readIdents = _2259_recIdents;
            } else {
              RAST._IExpr _2261_onExpr;
              DCOMP._IOwnership _2262_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2263_recIdents;
              RAST._IExpr _out539;
              DCOMP._IOwnership _out540;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
              (this).GenExpr(_2249_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out539, out _out540, out _out541);
              _2261_onExpr = _out539;
              _2262_onOwned = _out540;
              _2263_recIdents = _out541;
              r = _2261_onExpr;
              if (!object.Equals(_2261_onExpr, RAST.__default.self)) {
                RAST._IExpr _source114 = _2261_onExpr;
                bool unmatched114 = true;
                if (unmatched114) {
                  if (_source114.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source114.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source114.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name8 = underlying5.dtor_name;
                        if (object.Equals(name8, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          unmatched114 = false;
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                        }
                      }
                    }
                  }
                }
                if (unmatched114) {
                  unmatched114 = false;
                }
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeVar(_2250_field));
              if (_2251_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out542;
              DCOMP._IOwnership _out543;
              (this).FromOwned(r, expectedOwnership, out _out542, out _out543);
              r = _out542;
              resultingOwnership = _out543;
              readIdents = _2263_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_Index) {
          DAST._IExpression _2264_on = _source112.dtor_expr;
          DAST._ICollKind _2265_collKind = _source112.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2266_indices = _source112.dtor_indices;
          unmatched112 = false;
          {
            RAST._IExpr _2267_onExpr;
            DCOMP._IOwnership _2268_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2269_recIdents;
            RAST._IExpr _out544;
            DCOMP._IOwnership _out545;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out546;
            (this).GenExpr(_2264_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out544, out _out545, out _out546);
            _2267_onExpr = _out544;
            _2268_onOwned = _out545;
            _2269_recIdents = _out546;
            readIdents = _2269_recIdents;
            r = _2267_onExpr;
            bool _2270_hadArray;
            _2270_hadArray = false;
            if (object.Equals(_2265_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2270_hadArray = true;
              if ((new BigInteger((_2266_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi50 = new BigInteger((_2266_indices).Count);
            for (BigInteger _2271_i = BigInteger.Zero; _2271_i < _hi50; _2271_i++) {
              if (object.Equals(_2265_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2272_idx;
                DCOMP._IOwnership _2273_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2274_recIdentsIdx;
                RAST._IExpr _out547;
                DCOMP._IOwnership _out548;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
                (this).GenExpr((_2266_indices).Select(_2271_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out547, out _out548, out _out549);
                _2272_idx = _out547;
                _2273_idxOwned = _out548;
                _2274_recIdentsIdx = _out549;
                _2272_idx = RAST.__default.IntoUsize(_2272_idx);
                r = RAST.Expr.create_SelectIndex(r, _2272_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2274_recIdentsIdx);
              } else {
                RAST._IExpr _2275_idx;
                DCOMP._IOwnership _2276_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2277_recIdentsIdx;
                RAST._IExpr _out550;
                DCOMP._IOwnership _out551;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
                (this).GenExpr((_2266_indices).Select(_2271_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out550, out _out551, out _out552);
                _2275_idx = _out550;
                _2276_idxOwned = _out551;
                _2277_recIdentsIdx = _out552;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2275_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2277_recIdentsIdx);
              }
            }
            if (_2270_hadArray) {
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
      if (unmatched112) {
        if (_source112.is_IndexRange) {
          DAST._IExpression _2278_on = _source112.dtor_expr;
          bool _2279_isArray = _source112.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2280_low = _source112.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2281_high = _source112.dtor_high;
          unmatched112 = false;
          {
            RAST._IExpr _2282_onExpr;
            DCOMP._IOwnership _2283_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2284_recIdents;
            RAST._IExpr _out555;
            DCOMP._IOwnership _out556;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
            (this).GenExpr(_2278_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out555, out _out556, out _out557);
            _2282_onExpr = _out555;
            _2283_onOwned = _out556;
            _2284_recIdents = _out557;
            readIdents = _2284_recIdents;
            Dafny.ISequence<Dafny.Rune> _2285_methodName;
            _2285_methodName = (((_2280_low).is_Some) ? ((((_2281_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2281_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2286_arguments;
            _2286_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source115 = _2280_low;
            bool unmatched115 = true;
            if (unmatched115) {
              if (_source115.is_Some) {
                DAST._IExpression _2287_l = _source115.dtor_value;
                unmatched115 = false;
                {
                  RAST._IExpr _2288_lExpr;
                  DCOMP._IOwnership _2289___v201;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2290_recIdentsL;
                  RAST._IExpr _out558;
                  DCOMP._IOwnership _out559;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
                  (this).GenExpr(_2287_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out558, out _out559, out _out560);
                  _2288_lExpr = _out558;
                  _2289___v201 = _out559;
                  _2290_recIdentsL = _out560;
                  _2286_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2286_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2288_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2290_recIdentsL);
                }
              }
            }
            if (unmatched115) {
              unmatched115 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source116 = _2281_high;
            bool unmatched116 = true;
            if (unmatched116) {
              if (_source116.is_Some) {
                DAST._IExpression _2291_h = _source116.dtor_value;
                unmatched116 = false;
                {
                  RAST._IExpr _2292_hExpr;
                  DCOMP._IOwnership _2293___v202;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2294_recIdentsH;
                  RAST._IExpr _out561;
                  DCOMP._IOwnership _out562;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
                  (this).GenExpr(_2291_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out561, out _out562, out _out563);
                  _2292_hExpr = _out561;
                  _2293___v202 = _out562;
                  _2294_recIdentsH = _out563;
                  _2286_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2286_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2292_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2294_recIdentsH);
                }
              }
            }
            if (unmatched116) {
              unmatched116 = false;
            }
            r = _2282_onExpr;
            if (_2279_isArray) {
              if (!(_2285_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2285_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2285_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).FSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2285_methodName))).Apply(_2286_arguments);
            } else {
              if (!(_2285_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2285_methodName)).Apply(_2286_arguments);
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
      if (unmatched112) {
        if (_source112.is_TupleSelect) {
          DAST._IExpression _2295_on = _source112.dtor_expr;
          BigInteger _2296_idx = _source112.dtor_index;
          DAST._IType _2297_fieldType = _source112.dtor_fieldType;
          unmatched112 = false;
          {
            RAST._IExpr _2298_onExpr;
            DCOMP._IOwnership _2299_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2300_recIdents;
            RAST._IExpr _out566;
            DCOMP._IOwnership _out567;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
            (this).GenExpr(_2295_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out566, out _out567, out _out568);
            _2298_onExpr = _out566;
            _2299_onOwnership = _out567;
            _2300_recIdents = _out568;
            Dafny.ISequence<Dafny.Rune> _2301_selName;
            _2301_selName = Std.Strings.__default.OfNat(_2296_idx);
            DAST._IType _source117 = _2297_fieldType;
            bool unmatched117 = true;
            if (unmatched117) {
              if (_source117.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2302_tps = _source117.dtor_Tuple_a0;
                unmatched117 = false;
                if (((_2297_fieldType).is_Tuple) && ((new BigInteger((_2302_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2301_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2301_selName);
                }
              }
            }
            if (unmatched117) {
              unmatched117 = false;
            }
            r = ((_2298_onExpr).Sel(_2301_selName)).Clone();
            RAST._IExpr _out569;
            DCOMP._IOwnership _out570;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out569, out _out570);
            r = _out569;
            resultingOwnership = _out570;
            readIdents = _2300_recIdents;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_Call) {
          DAST._IExpression _2303_on = _source112.dtor_on;
          DAST._ICallName _2304_name = _source112.dtor_callName;
          Dafny.ISequence<DAST._IType> _2305_typeArgs = _source112.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2306_args = _source112.dtor_args;
          unmatched112 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2307_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2308_recIdents;
            Dafny.ISequence<RAST._IType> _2309_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2310_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out571;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out572;
            Dafny.ISequence<RAST._IType> _out573;
            Std.Wrappers._IOption<DAST._IResolvedType> _out574;
            (this).GenArgs(selfIdent, _2304_name, _2305_typeArgs, _2306_args, env, out _out571, out _out572, out _out573, out _out574);
            _2307_argExprs = _out571;
            _2308_recIdents = _out572;
            _2309_typeExprs = _out573;
            _2310_fullNameQualifier = _out574;
            readIdents = _2308_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source118 = _2310_fullNameQualifier;
            bool unmatched118 = true;
            if (unmatched118) {
              if (_source118.is_Some) {
                DAST._IResolvedType value11 = _source118.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2311_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2312_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2313_base = value11.dtor_kind;
                unmatched118 = false;
                RAST._IExpr _2314_fullPath;
                RAST._IExpr _out575;
                _out575 = DCOMP.COMP.GenPathExpr(_2311_path, true);
                _2314_fullPath = _out575;
                Dafny.ISequence<RAST._IType> _2315_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out576;
                _out576 = (this).GenTypeArgs(_2312_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2315_onTypeExprs = _out576;
                RAST._IExpr _2316_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2317_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2318_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2313_base).is_Trait) || ((_2313_base).is_Class)) {
                  RAST._IExpr _out577;
                  DCOMP._IOwnership _out578;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out579;
                  (this).GenExpr(_2303_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out577, out _out578, out _out579);
                  _2316_onExpr = _out577;
                  _2317_recOwnership = _out578;
                  _2318_recIdents = _out579;
                  _2316_onExpr = ((this).read__macro).Apply1(_2316_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2318_recIdents);
                } else {
                  RAST._IExpr _out580;
                  DCOMP._IOwnership _out581;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out582;
                  (this).GenExpr(_2303_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out580, out _out581, out _out582);
                  _2316_onExpr = _out580;
                  _2317_recOwnership = _out581;
                  _2318_recIdents = _out582;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2318_recIdents);
                }
                r = ((((_2314_fullPath).ApplyType(_2315_onTypeExprs)).FSel(DCOMP.__default.escapeName((_2304_name).dtor_name))).ApplyType(_2309_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2316_onExpr), _2307_argExprs));
                RAST._IExpr _out583;
                DCOMP._IOwnership _out584;
                (this).FromOwned(r, expectedOwnership, out _out583, out _out584);
                r = _out583;
                resultingOwnership = _out584;
              }
            }
            if (unmatched118) {
              unmatched118 = false;
              RAST._IExpr _2319_onExpr;
              DCOMP._IOwnership _2320___v208;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2321_recIdents;
              RAST._IExpr _out585;
              DCOMP._IOwnership _out586;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out587;
              (this).GenExpr(_2303_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out585, out _out586, out _out587);
              _2319_onExpr = _out585;
              _2320___v208 = _out586;
              _2321_recIdents = _out587;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2321_recIdents);
              Dafny.ISequence<Dafny.Rune> _2322_renderedName;
              _2322_renderedName = (this).GetMethodName(_2303_on, _2304_name);
              DAST._IExpression _source119 = _2303_on;
              bool unmatched119 = true;
              if (unmatched119) {
                bool disjunctiveMatch17 = false;
                if (_source119.is_Companion) {
                  disjunctiveMatch17 = true;
                }
                if (_source119.is_ExternCompanion) {
                  disjunctiveMatch17 = true;
                }
                if (disjunctiveMatch17) {
                  unmatched119 = false;
                  {
                    _2319_onExpr = (_2319_onExpr).FSel(_2322_renderedName);
                  }
                }
              }
              if (unmatched119) {
                unmatched119 = false;
                {
                  if (!object.Equals(_2319_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source120 = _2304_name;
                    bool unmatched120 = true;
                    if (unmatched120) {
                      if (_source120.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source120.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2323_tpe = onType2.dtor_value;
                          unmatched120 = false;
                          RAST._IType _2324_typ;
                          RAST._IType _out588;
                          _out588 = (this).GenType(_2323_tpe, DCOMP.GenTypeContext.@default());
                          _2324_typ = _out588;
                          if ((_2324_typ).IsObjectOrPointer()) {
                            _2319_onExpr = ((this).read__macro).Apply1(_2319_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched120) {
                      unmatched120 = false;
                    }
                  }
                  _2319_onExpr = (_2319_onExpr).Sel(_2322_renderedName);
                }
              }
              r = ((_2319_onExpr).ApplyType(_2309_typeExprs)).Apply(_2307_argExprs);
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
      if (unmatched112) {
        if (_source112.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2325_paramsDafny = _source112.dtor_params;
          DAST._IType _2326_retType = _source112.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2327_body = _source112.dtor_body;
          unmatched112 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2328_params;
            Dafny.ISequence<RAST._IFormal> _out591;
            _out591 = (this).GenParams(_2325_paramsDafny, true);
            _2328_params = _out591;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2329_paramNames;
            _2329_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2330_paramTypesMap;
            _2330_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi51 = new BigInteger((_2328_params).Count);
            for (BigInteger _2331_i = BigInteger.Zero; _2331_i < _hi51; _2331_i++) {
              Dafny.ISequence<Dafny.Rune> _2332_name;
              _2332_name = ((_2328_params).Select(_2331_i)).dtor_name;
              _2329_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2329_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2332_name));
              _2330_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2330_paramTypesMap, _2332_name, ((_2328_params).Select(_2331_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2333_subEnv;
            _2333_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2329_paramNames, _2330_paramTypesMap));
            RAST._IExpr _2334_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2335_recIdents;
            DCOMP._IEnvironment _2336___v218;
            RAST._IExpr _out592;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out593;
            DCOMP._IEnvironment _out594;
            (this).GenStmts(_2327_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2333_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out592, out _out593, out _out594);
            _2334_recursiveGen = _out592;
            _2335_recIdents = _out593;
            _2336___v218 = _out594;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2335_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2335_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2337_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll10 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_11 in (_2337_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2338_name = (Dafny.ISequence<Dafny.Rune>)_compr_11;
                if ((_2337_paramNames).Contains(_2338_name)) {
                  _coll10.Add(_2338_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll10);
            }))())(_2329_paramNames));
            RAST._IExpr _2339_allReadCloned;
            _2339_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2335_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2340_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_4 in (_2335_recIdents).Elements) {
                _2340_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_4;
                if ((_2335_recIdents).Contains(_2340_next)) {
                  goto after__ASSIGN_SUCH_THAT_4;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 5313)");
            after__ASSIGN_SUCH_THAT_4: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2340_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2341_selfCloned;
                DCOMP._IOwnership _2342___v219;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2343___v220;
                RAST._IExpr _out595;
                DCOMP._IOwnership _out596;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out597;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out595, out _out596, out _out597);
                _2341_selfCloned = _out595;
                _2342___v219 = _out596;
                _2343___v220 = _out597;
                _2339_allReadCloned = (_2339_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2341_selfCloned)));
              } else if (!((_2329_paramNames).Contains(_2340_next))) {
                RAST._IExpr _2344_copy;
                _2344_copy = (RAST.Expr.create_Identifier(_2340_next)).Clone();
                _2339_allReadCloned = (_2339_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2340_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2344_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2340_next));
              }
              _2335_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2335_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2340_next));
            }
            RAST._IType _2345_retTypeGen;
            RAST._IType _out598;
            _out598 = (this).GenType(_2326_retType, DCOMP.GenTypeContext.@default());
            _2345_retTypeGen = _out598;
            r = RAST.Expr.create_Block((_2339_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2328_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2345_retTypeGen), RAST.Expr.create_Block(_2334_recursiveGen)))));
            RAST._IExpr _out599;
            DCOMP._IOwnership _out600;
            (this).FromOwned(r, expectedOwnership, out _out599, out _out600);
            r = _out599;
            resultingOwnership = _out600;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2346_values = _source112.dtor_values;
          DAST._IType _2347_retType = _source112.dtor_retType;
          DAST._IExpression _2348_expr = _source112.dtor_expr;
          unmatched112 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2349_paramNames;
            _2349_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2350_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out601;
            _out601 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2351_value) => {
              return (_2351_value).dtor__0;
            })), _2346_values), false);
            _2350_paramFormals = _out601;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2352_paramTypes;
            _2352_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2353_paramNamesSet;
            _2353_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi52 = new BigInteger((_2346_values).Count);
            for (BigInteger _2354_i = BigInteger.Zero; _2354_i < _hi52; _2354_i++) {
              Dafny.ISequence<Dafny.Rune> _2355_name;
              _2355_name = (((_2346_values).Select(_2354_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2356_rName;
              _2356_rName = DCOMP.__default.escapeVar(_2355_name);
              _2349_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2349_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2356_rName));
              _2352_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2352_paramTypes, _2356_rName, ((_2350_paramFormals).Select(_2354_i)).dtor_tpe);
              _2353_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2353_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2356_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi53 = new BigInteger((_2346_values).Count);
            for (BigInteger _2357_i = BigInteger.Zero; _2357_i < _hi53; _2357_i++) {
              RAST._IType _2358_typeGen;
              RAST._IType _out602;
              _out602 = (this).GenType((((_2346_values).Select(_2357_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.@default());
              _2358_typeGen = _out602;
              RAST._IExpr _2359_valueGen;
              DCOMP._IOwnership _2360___v221;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2361_recIdents;
              RAST._IExpr _out603;
              DCOMP._IOwnership _out604;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out605;
              (this).GenExpr(((_2346_values).Select(_2357_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out603, out _out604, out _out605);
              _2359_valueGen = _out603;
              _2360___v221 = _out604;
              _2361_recIdents = _out605;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar((((_2346_values).Select(_2357_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2358_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2359_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2361_recIdents);
            }
            DCOMP._IEnvironment _2362_newEnv;
            _2362_newEnv = DCOMP.Environment.create(_2349_paramNames, _2352_paramTypes);
            RAST._IExpr _2363_recGen;
            DCOMP._IOwnership _2364_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2365_recIdents;
            RAST._IExpr _out606;
            DCOMP._IOwnership _out607;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out608;
            (this).GenExpr(_2348_expr, selfIdent, _2362_newEnv, expectedOwnership, out _out606, out _out607, out _out608);
            _2363_recGen = _out606;
            _2364_recOwned = _out607;
            _2365_recIdents = _out608;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2365_recIdents, _2353_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2363_recGen));
            RAST._IExpr _out609;
            DCOMP._IOwnership _out610;
            (this).FromOwnership(r, _2364_recOwned, expectedOwnership, out _out609, out _out610);
            r = _out609;
            resultingOwnership = _out610;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2366_name = _source112.dtor_ident;
          DAST._IType _2367_tpe = _source112.dtor_typ;
          DAST._IExpression _2368_value = _source112.dtor_value;
          DAST._IExpression _2369_iifeBody = _source112.dtor_iifeBody;
          unmatched112 = false;
          {
            RAST._IExpr _2370_valueGen;
            DCOMP._IOwnership _2371___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2372_recIdents;
            RAST._IExpr _out611;
            DCOMP._IOwnership _out612;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out613;
            (this).GenExpr(_2368_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out611, out _out612, out _out613);
            _2370_valueGen = _out611;
            _2371___v222 = _out612;
            _2372_recIdents = _out613;
            readIdents = _2372_recIdents;
            RAST._IType _2373_valueTypeGen;
            RAST._IType _out614;
            _out614 = (this).GenType(_2367_tpe, DCOMP.GenTypeContext.@default());
            _2373_valueTypeGen = _out614;
            Dafny.ISequence<Dafny.Rune> _2374_iifeVar;
            _2374_iifeVar = DCOMP.__default.escapeVar(_2366_name);
            RAST._IExpr _2375_bodyGen;
            DCOMP._IOwnership _2376___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2377_bodyIdents;
            RAST._IExpr _out615;
            DCOMP._IOwnership _out616;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out617;
            (this).GenExpr(_2369_iifeBody, selfIdent, (env).AddAssigned(_2374_iifeVar, _2373_valueTypeGen), DCOMP.Ownership.create_OwnershipOwned(), out _out615, out _out616, out _out617);
            _2375_bodyGen = _out615;
            _2376___v223 = _out616;
            _2377_bodyIdents = _out617;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2377_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2374_iifeVar)));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _2374_iifeVar, Std.Wrappers.Option<RAST._IType>.create_Some(_2373_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2370_valueGen))).Then(_2375_bodyGen));
            RAST._IExpr _out618;
            DCOMP._IOwnership _out619;
            (this).FromOwned(r, expectedOwnership, out _out618, out _out619);
            r = _out618;
            resultingOwnership = _out619;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_Apply) {
          DAST._IExpression _2378_func = _source112.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2379_args = _source112.dtor_args;
          unmatched112 = false;
          {
            RAST._IExpr _2380_funcExpr;
            DCOMP._IOwnership _2381___v224;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2382_recIdents;
            RAST._IExpr _out620;
            DCOMP._IOwnership _out621;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
            (this).GenExpr(_2378_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out620, out _out621, out _out622);
            _2380_funcExpr = _out620;
            _2381___v224 = _out621;
            _2382_recIdents = _out622;
            readIdents = _2382_recIdents;
            Dafny.ISequence<RAST._IExpr> _2383_rArgs;
            _2383_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi54 = new BigInteger((_2379_args).Count);
            for (BigInteger _2384_i = BigInteger.Zero; _2384_i < _hi54; _2384_i++) {
              RAST._IExpr _2385_argExpr;
              DCOMP._IOwnership _2386_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2387_argIdents;
              RAST._IExpr _out623;
              DCOMP._IOwnership _out624;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out625;
              (this).GenExpr((_2379_args).Select(_2384_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out623, out _out624, out _out625);
              _2385_argExpr = _out623;
              _2386_argOwned = _out624;
              _2387_argIdents = _out625;
              _2383_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2383_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2385_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2387_argIdents);
            }
            r = (_2380_funcExpr).Apply(_2383_rArgs);
            RAST._IExpr _out626;
            DCOMP._IOwnership _out627;
            (this).FromOwned(r, expectedOwnership, out _out626, out _out627);
            r = _out626;
            resultingOwnership = _out627;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_TypeTest) {
          DAST._IExpression _2388_on = _source112.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2389_dType = _source112.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2390_variant = _source112.dtor_variant;
          unmatched112 = false;
          {
            RAST._IExpr _2391_exprGen;
            DCOMP._IOwnership _2392___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2393_recIdents;
            RAST._IExpr _out628;
            DCOMP._IOwnership _out629;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out630;
            (this).GenExpr(_2388_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out628, out _out629, out _out630);
            _2391_exprGen = _out628;
            _2392___v225 = _out629;
            _2393_recIdents = _out630;
            RAST._IType _2394_dTypePath;
            RAST._IType _out631;
            _out631 = DCOMP.COMP.GenPathType(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2389_dType, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2390_variant)));
            _2394_dTypePath = _out631;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2391_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_2394_dTypePath)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out632;
            DCOMP._IOwnership _out633;
            (this).FromOwned(r, expectedOwnership, out _out632, out _out633);
            r = _out632;
            resultingOwnership = _out633;
            readIdents = _2393_recIdents;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_Is) {
          DAST._IExpression _2395_expr = _source112.dtor_expr;
          DAST._IType _2396_fromType = _source112.dtor_fromType;
          DAST._IType _2397_toType = _source112.dtor_toType;
          unmatched112 = false;
          {
            RAST._IExpr _2398_expr;
            DCOMP._IOwnership _2399_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2400_recIdents;
            RAST._IExpr _out634;
            DCOMP._IOwnership _out635;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out636;
            (this).GenExpr(_2395_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out634, out _out635, out _out636);
            _2398_expr = _out634;
            _2399_recOwned = _out635;
            _2400_recIdents = _out636;
            RAST._IType _2401_fromType;
            RAST._IType _out637;
            _out637 = (this).GenType(_2396_fromType, DCOMP.GenTypeContext.@default());
            _2401_fromType = _out637;
            RAST._IType _2402_toType;
            RAST._IType _out638;
            _out638 = (this).GenType(_2397_toType, DCOMP.GenTypeContext.@default());
            _2402_toType = _out638;
            if (((_2401_fromType).IsObjectOrPointer()) && ((_2402_toType).IsObjectOrPointer())) {
              r = (((_2398_expr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is_instance_of"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((_2402_toType).ObjectOrPointerUnderlying()))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Source and/or target types of type test is/are not Object or Ptr"));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
            RAST._IExpr _out639;
            DCOMP._IOwnership _out640;
            (this).FromOwnership(r, _2399_recOwned, expectedOwnership, out _out639, out _out640);
            r = _out639;
            resultingOwnership = _out640;
            readIdents = _2400_recIdents;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_BoolBoundedPool) {
          unmatched112 = false;
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
      if (unmatched112) {
        if (_source112.is_SetBoundedPool) {
          DAST._IExpression _2403_of = _source112.dtor_of;
          unmatched112 = false;
          {
            RAST._IExpr _2404_exprGen;
            DCOMP._IOwnership _2405___v226;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2406_recIdents;
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out645;
            (this).GenExpr(_2403_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out643, out _out644, out _out645);
            _2404_exprGen = _out643;
            _2405___v226 = _out644;
            _2406_recIdents = _out645;
            r = ((_2404_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out646;
            DCOMP._IOwnership _out647;
            (this).FromOwned(r, expectedOwnership, out _out646, out _out647);
            r = _out646;
            resultingOwnership = _out647;
            readIdents = _2406_recIdents;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_SeqBoundedPool) {
          DAST._IExpression _2407_of = _source112.dtor_of;
          bool _2408_includeDuplicates = _source112.dtor_includeDuplicates;
          unmatched112 = false;
          {
            RAST._IExpr _2409_exprGen;
            DCOMP._IOwnership _2410___v227;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2411_recIdents;
            RAST._IExpr _out648;
            DCOMP._IOwnership _out649;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out650;
            (this).GenExpr(_2407_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out648, out _out649, out _out650);
            _2409_exprGen = _out648;
            _2410___v227 = _out649;
            _2411_recIdents = _out650;
            r = ((_2409_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2408_includeDuplicates)) {
              r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).AsExpr()).Apply1(r);
            }
            RAST._IExpr _out651;
            DCOMP._IOwnership _out652;
            (this).FromOwned(r, expectedOwnership, out _out651, out _out652);
            r = _out651;
            resultingOwnership = _out652;
            readIdents = _2411_recIdents;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_MapBoundedPool) {
          DAST._IExpression _2412_of = _source112.dtor_of;
          unmatched112 = false;
          {
            RAST._IExpr _2413_exprGen;
            DCOMP._IOwnership _2414___v228;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2415_recIdents;
            RAST._IExpr _out653;
            DCOMP._IOwnership _out654;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
            (this).GenExpr(_2412_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out653, out _out654, out _out655);
            _2413_exprGen = _out653;
            _2414___v228 = _out654;
            _2415_recIdents = _out655;
            r = ((((_2413_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2415_recIdents;
            RAST._IExpr _out656;
            DCOMP._IOwnership _out657;
            (this).FromOwned(r, expectedOwnership, out _out656, out _out657);
            r = _out656;
            resultingOwnership = _out657;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_IntRange) {
          DAST._IType _2416_typ = _source112.dtor_elemType;
          DAST._IExpression _2417_lo = _source112.dtor_lo;
          DAST._IExpression _2418_hi = _source112.dtor_hi;
          bool _2419_up = _source112.dtor_up;
          unmatched112 = false;
          {
            RAST._IExpr _2420_lo;
            DCOMP._IOwnership _2421___v229;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2422_recIdentsLo;
            RAST._IExpr _out658;
            DCOMP._IOwnership _out659;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out660;
            (this).GenExpr(_2417_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out658, out _out659, out _out660);
            _2420_lo = _out658;
            _2421___v229 = _out659;
            _2422_recIdentsLo = _out660;
            RAST._IExpr _2423_hi;
            DCOMP._IOwnership _2424___v230;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2425_recIdentsHi;
            RAST._IExpr _out661;
            DCOMP._IOwnership _out662;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out663;
            (this).GenExpr(_2418_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out661, out _out662, out _out663);
            _2423_hi = _out661;
            _2424___v230 = _out662;
            _2425_recIdentsHi = _out663;
            if (_2419_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2420_lo, _2423_hi));
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2423_hi, _2420_lo));
            }
            if (!((_2416_typ).is_Primitive)) {
              RAST._IType _2426_tpe;
              RAST._IType _out664;
              _out664 = (this).GenType(_2416_typ, DCOMP.GenTypeContext.@default());
              _2426_tpe = _out664;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map"))).Apply1((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2426_tpe))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into")));
            }
            RAST._IExpr _out665;
            DCOMP._IOwnership _out666;
            (this).FromOwned(r, expectedOwnership, out _out665, out _out666);
            r = _out665;
            resultingOwnership = _out666;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2422_recIdentsLo, _2425_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_UnboundedIntRange) {
          DAST._IExpression _2427_start = _source112.dtor_start;
          bool _2428_up = _source112.dtor_up;
          unmatched112 = false;
          {
            RAST._IExpr _2429_start;
            DCOMP._IOwnership _2430___v231;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2431_recIdentStart;
            RAST._IExpr _out667;
            DCOMP._IOwnership _out668;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out669;
            (this).GenExpr(_2427_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out667, out _out668, out _out669);
            _2429_start = _out667;
            _2430___v231 = _out668;
            _2431_recIdentStart = _out669;
            if (_2428_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).AsExpr()).Apply1(_2429_start);
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).AsExpr()).Apply1(_2429_start);
            }
            RAST._IExpr _out670;
            DCOMP._IOwnership _out671;
            (this).FromOwned(r, expectedOwnership, out _out670, out _out671);
            r = _out670;
            resultingOwnership = _out671;
            readIdents = _2431_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_MapBuilder) {
          DAST._IType _2432_keyType = _source112.dtor_keyType;
          DAST._IType _2433_valueType = _source112.dtor_valueType;
          unmatched112 = false;
          {
            RAST._IType _2434_kType;
            RAST._IType _out672;
            _out672 = (this).GenType(_2432_keyType, DCOMP.GenTypeContext.@default());
            _2434_kType = _out672;
            RAST._IType _2435_vType;
            RAST._IType _out673;
            _out673 = (this).GenType(_2433_valueType, DCOMP.GenTypeContext.@default());
            _2435_vType = _out673;
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2434_kType, _2435_vType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out674;
            DCOMP._IOwnership _out675;
            (this).FromOwned(r, expectedOwnership, out _out674, out _out675);
            r = _out674;
            resultingOwnership = _out675;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched112) {
        if (_source112.is_SetBuilder) {
          DAST._IType _2436_elemType = _source112.dtor_elemType;
          unmatched112 = false;
          {
            RAST._IType _2437_eType;
            RAST._IType _out676;
            _out676 = (this).GenType(_2436_elemType, DCOMP.GenTypeContext.@default());
            _2437_eType = _out676;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2437_eType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out677;
            DCOMP._IOwnership _out678;
            (this).FromOwned(r, expectedOwnership, out _out677, out _out678);
            r = _out677;
            resultingOwnership = _out678;
            return ;
          }
        }
      }
      if (unmatched112) {
        DAST._IType _2438_elemType = _source112.dtor_elemType;
        DAST._IExpression _2439_collection = _source112.dtor_collection;
        bool _2440_is__forall = _source112.dtor_is__forall;
        DAST._IExpression _2441_lambda = _source112.dtor_lambda;
        unmatched112 = false;
        {
          RAST._IType _2442_tpe;
          RAST._IType _out679;
          _out679 = (this).GenType(_2438_elemType, DCOMP.GenTypeContext.@default());
          _2442_tpe = _out679;
          RAST._IExpr _2443_collectionGen;
          DCOMP._IOwnership _2444___v232;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2445_recIdents;
          RAST._IExpr _out680;
          DCOMP._IOwnership _out681;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out682;
          (this).GenExpr(_2439_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out680, out _out681, out _out682);
          _2443_collectionGen = _out680;
          _2444___v232 = _out681;
          _2445_recIdents = _out682;
          Dafny.ISequence<DAST._IAttribute> _2446_extraAttributes;
          _2446_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2439_collection).is_IntRange) || ((_2439_collection).is_UnboundedIntRange)) || ((_2439_collection).is_SeqBoundedPool)) {
            _2446_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2441_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2447_formals;
            _2447_formals = (_2441_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2448_newFormals;
            _2448_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi55 = new BigInteger((_2447_formals).Count);
            for (BigInteger _2449_i = BigInteger.Zero; _2449_i < _hi55; _2449_i++) {
              var _pat_let_tv201 = _2446_extraAttributes;
              var _pat_let_tv202 = _2447_formals;
              _2448_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2448_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2447_formals).Select(_2449_i), _pat_let29_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let29_0, _2450_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv201, ((_pat_let_tv202).Select(_2449_i)).dtor_attributes), _pat_let30_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let30_0, _2451_dt__update_hattributes_h0 => DAST.Formal.create((_2450_dt__update__tmp_h0).dtor_name, (_2450_dt__update__tmp_h0).dtor_typ, _2451_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv203 = _2448_newFormals;
            DAST._IExpression _2452_newLambda;
            _2452_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2441_lambda, _pat_let31_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let31_0, _2453_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv203, _pat_let32_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let32_0, _2454_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2454_dt__update_hparams_h0, (_2453_dt__update__tmp_h1).dtor_retType, (_2453_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2455_lambdaGen;
            DCOMP._IOwnership _2456___v233;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2457_recLambdaIdents;
            RAST._IExpr _out683;
            DCOMP._IOwnership _out684;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out685;
            (this).GenExpr(_2452_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out683, out _out684, out _out685);
            _2455_lambdaGen = _out683;
            _2456___v233 = _out684;
            _2457_recLambdaIdents = _out685;
            Dafny.ISequence<Dafny.Rune> _2458_fn;
            _2458_fn = ((_2440_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2443_collectionGen).Sel(_2458_fn)).Apply1(((_2455_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2445_recIdents, _2457_recLambdaIdents);
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Quantifier without an inline lambda"));
            r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
          RAST._IExpr _out686;
          DCOMP._IOwnership _out687;
          (this).FromOwned(r, expectedOwnership, out _out686, out _out687);
          r = _out686;
          resultingOwnership = _out687;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> externalFiles)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      Dafny.ISequence<RAST._IModDecl> _2459_externUseDecls;
      _2459_externUseDecls = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi56 = new BigInteger((externalFiles).Count);
      for (BigInteger _2460_i = BigInteger.Zero; _2460_i < _hi56; _2460_i++) {
        Dafny.ISequence<Dafny.Rune> _2461_externalFile;
        _2461_externalFile = (externalFiles).Select(_2460_i);
        Dafny.ISequence<Dafny.Rune> _2462_externalMod;
        _2462_externalMod = _2461_externalFile;
        if (((new BigInteger((_2461_externalFile).Count)) > (new BigInteger(3))) && (((_2461_externalFile).Drop((new BigInteger((_2461_externalFile).Count)) - (new BigInteger(3)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".rs")))) {
          _2462_externalMod = (_2461_externalFile).Subsequence(BigInteger.Zero, (new BigInteger((_2461_externalFile).Count)) - (new BigInteger(3)));
        } else {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unrecognized external file "), _2461_externalFile), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". External file must be *.rs files")));
        }
        RAST._IMod _2463_externMod;
        _2463_externMod = RAST.Mod.create_ExternMod(_2462_externalMod);
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (_2463_externMod)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        _2459_externUseDecls = Dafny.Sequence<RAST._IModDecl>.Concat(_2459_externUseDecls, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), ((RAST.__default.crate).MSel(_2462_externalMod)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))));
      }
      if (!(_2459_externUseDecls).Equals(Dafny.Sequence<RAST._IModDecl>.FromElements())) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (RAST.Mod.create_Mod(DCOMP.COMP.DAFNY__EXTERN__MODULE, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _2459_externUseDecls))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
      }
      DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _2464_allModules;
      _2464_allModules = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Empty();
      BigInteger _hi57 = new BigInteger((p).Count);
      for (BigInteger _2465_i = BigInteger.Zero; _2465_i < _hi57; _2465_i++) {
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _2466_m;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out688;
        _out688 = (this).GenModule((p).Select(_2465_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2466_m = _out688;
        _2464_allModules = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(_2464_allModules, _2466_m);
      }
      BigInteger _hi58 = new BigInteger(((_2464_allModules).dtor_keys).Count);
      for (BigInteger _2467_i = BigInteger.Zero; _2467_i < _hi58; _2467_i++) {
        if (!((_2464_allModules).dtor_values).Contains(((_2464_allModules).dtor_keys).Select(_2467_i))) {
          goto continue_0;
        }
        RAST._IMod _2468_m;
        _2468_m = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Select((_2464_allModules).dtor_values,((_2464_allModules).dtor_keys).Select(_2467_i))).ToRust();
        BigInteger _hi59 = new BigInteger((this.optimizations).Count);
        for (BigInteger _2469_j = BigInteger.Zero; _2469_j < _hi59; _2469_j++) {
          _2468_m = Dafny.Helpers.Id<Func<RAST._IMod, RAST._IMod>>((this.optimizations).Select(_2469_j))(_2468_m);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (_2468_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      continue_0: ;
      }
    after_0: ;
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2470_i;
      _2470_i = BigInteger.Zero;
      while ((_2470_i) < (new BigInteger((fullName).Count))) {
        if ((_2470_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2470_i)));
        _2470_i = (_2470_i) + (BigInteger.One);
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
    public static Dafny.ISequence<Dafny.Rune> TailRecursionPrefix { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_r");
    } }
    public static Dafny.ISequence<Dafny.Rune> DAFNY__EXTERN__MODULE { get {
      return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_dafny_externs");
    } }
  }
} // end of namespace DCOMP