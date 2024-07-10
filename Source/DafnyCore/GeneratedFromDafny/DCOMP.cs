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
      Dafny.ISequence<Dafny.Rune> _1290___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1290___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1290___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1290___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in137 = (i).Drop(new BigInteger(2));
        i = _in137;
        goto TAIL_CALL_START;
      } else {
        _1290___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1290___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in138 = (i).Drop(BigInteger.One);
        i = _in138;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1291___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1291___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1291___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1291___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in139 = (i).Drop(BigInteger.One);
        i = _in139;
        goto TAIL_CALL_START;
      } else {
        _1291___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1291___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1292_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1292_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeVar(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1293_r = (f);
      if ((DCOMP.__default.reserved__vars).Contains(_1293_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1293_r);
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
      var _pat_let_tv187 = dafnyName;
      var _pat_let_tv188 = rs;
      var _pat_let_tv189 = dafnyName;
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _1294_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source65 = (rs).Select(BigInteger.Zero);
          bool unmatched65 = true;
          if (unmatched65) {
            if (_source65.is_UserDefined) {
              DAST._IResolvedType _1295_resolvedType = _source65.dtor_resolved;
              unmatched65 = false;
              return DCOMP.__default.TraitTypeContainingMethod(_1295_resolvedType, _pat_let_tv187);
            }
          }
          if (unmatched65) {
            unmatched65 = false;
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
          throw new System.Exception("unexpected control point");
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source66 = _1294_res;
        bool unmatched66 = true;
        if (unmatched66) {
          if (_source66.is_Some) {
            unmatched66 = false;
            return _1294_res;
          }
        }
        if (unmatched66) {
          unmatched66 = false;
          return DCOMP.__default.TraitTypeContainingMethodAux((_pat_let_tv188).Drop(BigInteger.One), _pat_let_tv189);
        }
        throw new System.Exception("unexpected control point");
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethod(DAST._IResolvedType r, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DAST._IResolvedType _let_tmp_rhs53 = r;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1296_path = _let_tmp_rhs53.dtor_path;
      Dafny.ISequence<DAST._IType> _1297_typeArgs = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedTypeBase _1298_kind = _let_tmp_rhs53.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1299_attributes = _let_tmp_rhs53.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1300_properMethods = _let_tmp_rhs53.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1301_extendedTypes = _let_tmp_rhs53.dtor_extendedTypes;
      if ((_1300_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1301_extendedTypes, dafnyName);
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
      Dafny.ISequence<Dafny.Rune> _1302___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1302___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((s).Select(BigInteger.Zero)) == (new Dafny.Rune(' '))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1302___accumulator, s);
      } else {
        _1302___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1302___accumulator, ((((s).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")) : (Dafny.Sequence<Dafny.Rune>.FromElements((s).Select(BigInteger.Zero)))));
        Dafny.ISequence<Dafny.Rune> _in141 = (s).Drop(BigInteger.One);
        s = _in141;
        goto TAIL_CALL_START;
      }
    }
    public static DCOMP._IExternAttribute ExtractExtern(Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DCOMP._IExternAttribute res = DCOMP.ExternAttribute.Default();
      BigInteger _hi5 = new BigInteger((attributes).Count);
      for (BigInteger _1303_i = BigInteger.Zero; _1303_i < _hi5; _1303_i++) {
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _1304_attr;
        _1304_attr = DCOMP.__default.OptExtern((attributes).Select(_1303_i), dafnyName);
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _source67 = _1304_attr;
        bool unmatched67 = true;
        if (unmatched67) {
          if (_source67.is_Some) {
            DCOMP._IExternAttribute _1305_n = _source67.dtor_value;
            unmatched67 = false;
            res = _1305_n;
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
      DCOMP._IEnvironment _1306_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1307_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll8 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_9 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1308_k = (Dafny.ISequence<Dafny.Rune>)_compr_9;
          if (((this).dtor_types).Contains(_1308_k)) {
            _coll8.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_1308_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_1308_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll8);
      }))();
      return DCOMP.Environment.create((_1306_dt__update__tmp_h0).dtor_names, _1307_dt__update_htypes_h0);
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
      BigInteger _1309_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1309_indexInEnv), ((this).dtor_names).Drop((_1309_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      return Std.Collections.Seq.__default.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1310_i) => {
        return DCOMP.__default.escapeName((_1310_i));
      })), containingPath);
    }
    public DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> s = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Default();
      _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs54 = DafnyCompilerRustUtils.__default.DafnyNameToContainingPathAndName((mod).dtor_name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1311_innerPath = _let_tmp_rhs54.dtor__0;
      Dafny.ISequence<Dafny.Rune> _1312_innerName = _let_tmp_rhs54.dtor__1;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1313_containingPath;
      _1313_containingPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, _1311_innerPath);
      Dafny.ISequence<Dafny.Rune> _1314_modName;
      _1314_modName = DCOMP.__default.escapeName(_1312_innerName);
      if (((mod).dtor_body).is_None) {
        s = DafnyCompilerRustUtils.GatheringModule.Wrap(DCOMP.COMP.ContainingPathToRust(_1313_containingPath), RAST.Mod.create_ExternMod(_1314_modName));
      } else {
        DCOMP._IExternAttribute _1315_optExtern;
        _1315_optExtern = DCOMP.__default.ExtractExternMod(mod);
        Dafny.ISequence<RAST._IModDecl> _1316_body;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _1317_allmodules;
        Dafny.ISequence<RAST._IModDecl> _out15;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out16;
        (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1313_containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1312_innerName)), out _out15, out _out16);
        _1316_body = _out15;
        _1317_allmodules = _out16;
        if ((_1315_optExtern).is_SimpleExtern) {
          if ((mod).dtor_requiresExterns) {
            _1316_body = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (((RAST.__default.crate).MSel(DCOMP.COMP.DAFNY__EXTERN__MODULE)).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1315_optExtern).dtor_overrideName))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))), _1316_body);
          }
        } else if ((_1315_optExtern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Externs on modules can only have 1 string argument"));
        } else if ((_1315_optExtern).is_UnsupportedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some((_1315_optExtern).dtor_reason);
        }
        s = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(DafnyCompilerRustUtils.GatheringModule.Wrap(DCOMP.COMP.ContainingPathToRust(_1313_containingPath), RAST.Mod.create_Mod(_1314_modName, _1316_body)), _1317_allmodules);
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
      for (BigInteger _1318_i = BigInteger.Zero; _1318_i < _hi6; _1318_i++) {
        Dafny.ISequence<RAST._IModDecl> _1319_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source68 = (body).Select(_1318_i);
        bool unmatched68 = true;
        if (unmatched68) {
          if (_source68.is_Module) {
            DAST._IModule _1320_m = _source68.dtor_Module_a0;
            unmatched68 = false;
            DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _1321_mm;
            DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out17;
            _out17 = (this).GenModule(_1320_m, containingPath);
            _1321_mm = _out17;
            allmodules = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(allmodules, _1321_mm);
            _1319_generated = Dafny.Sequence<RAST._IModDecl>.FromElements();
          }
        }
        if (unmatched68) {
          if (_source68.is_Class) {
            DAST._IClass _1322_c = _source68.dtor_Class_a0;
            unmatched68 = false;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenClass(_1322_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1322_c).dtor_name)));
            _1319_generated = _out18;
          }
        }
        if (unmatched68) {
          if (_source68.is_Trait) {
            DAST._ITrait _1323_t = _source68.dtor_Trait_a0;
            unmatched68 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenTrait(_1323_t, containingPath);
            _1319_generated = _out19;
          }
        }
        if (unmatched68) {
          if (_source68.is_Newtype) {
            DAST._INewtype _1324_n = _source68.dtor_Newtype_a0;
            unmatched68 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenNewtype(_1324_n);
            _1319_generated = _out20;
          }
        }
        if (unmatched68) {
          if (_source68.is_SynonymType) {
            DAST._ISynonymType _1325_s = _source68.dtor_SynonymType_a0;
            unmatched68 = false;
            Dafny.ISequence<RAST._IModDecl> _out21;
            _out21 = (this).GenSynonymType(_1325_s);
            _1319_generated = _out21;
          }
        }
        if (unmatched68) {
          DAST._IDatatype _1326_d = _source68.dtor_Datatype_a0;
          unmatched68 = false;
          Dafny.ISequence<RAST._IModDecl> _out22;
          _out22 = (this).GenDatatype(_1326_d);
          _1319_generated = _out22;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1319_generated);
      }
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1327_genTpConstraint;
      _1327_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1327_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1327_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1327_genTpConstraint);
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
        for (BigInteger _1328_tpI = BigInteger.Zero; _1328_tpI < _hi7; _1328_tpI++) {
          DAST._ITypeArgDecl _1329_tp;
          _1329_tp = (@params).Select(_1328_tpI);
          DAST._IType _1330_typeArg;
          RAST._ITypeParamDecl _1331_typeParam;
          DAST._IType _out23;
          RAST._ITypeParamDecl _out24;
          (this).GenTypeParam(_1329_tp, out _out23, out _out24);
          _1330_typeArg = _out23;
          _1331_typeParam = _out24;
          RAST._IType _1332_rType;
          RAST._IType _out25;
          _out25 = (this).GenType(_1330_typeArg, DCOMP.GenTypeContext.@default());
          _1332_rType = _out25;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1330_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1332_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1331_typeParam));
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
      Dafny.ISequence<DAST._IType> _1333_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1334_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1335_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1336_whereConstraints;
      Dafny.ISequence<DAST._IType> _out26;
      Dafny.ISequence<RAST._IType> _out27;
      Dafny.ISequence<RAST._ITypeParamDecl> _out28;
      Dafny.ISequence<Dafny.Rune> _out29;
      (this).GenTypeParameters((c).dtor_typeParams, out _out26, out _out27, out _out28, out _out29);
      _1333_typeParamsSeq = _out26;
      _1334_rTypeParams = _out27;
      _1335_rTypeParamsDecls = _out28;
      _1336_whereConstraints = _out29;
      Dafny.ISequence<Dafny.Rune> _1337_constrainedTypeParams;
      _1337_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1335_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1338_fields;
      _1338_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1339_fieldInits;
      _1339_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi8 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1340_fieldI = BigInteger.Zero; _1340_fieldI < _hi8; _1340_fieldI++) {
        DAST._IField _1341_field;
        _1341_field = ((c).dtor_fields).Select(_1340_fieldI);
        RAST._IType _1342_fieldType;
        RAST._IType _out30;
        _out30 = (this).GenType(((_1341_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1342_fieldType = _out30;
        Dafny.ISequence<Dafny.Rune> _1343_fieldRustName;
        _1343_fieldRustName = DCOMP.__default.escapeVar(((_1341_field).dtor_formal).dtor_name);
        _1338_fields = Dafny.Sequence<RAST._IField>.Concat(_1338_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1343_fieldRustName, _1342_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source69 = (_1341_field).dtor_defaultValue;
        bool unmatched69 = true;
        if (unmatched69) {
          if (_source69.is_Some) {
            DAST._IExpression _1344_e = _source69.dtor_value;
            unmatched69 = false;
            {
              RAST._IExpr _1345_expr;
              DCOMP._IOwnership _1346___v51;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1347___v52;
              RAST._IExpr _out31;
              DCOMP._IOwnership _out32;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out33;
              (this).GenExpr(_1344_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out31, out _out32, out _out33);
              _1345_expr = _out31;
              _1346___v51 = _out32;
              _1347___v52 = _out33;
              _1339_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1339_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1343_fieldRustName, _1345_expr)));
            }
          }
        }
        if (unmatched69) {
          unmatched69 = false;
          {
            RAST._IExpr _1348_default;
            _1348_default = RAST.__default.std__Default__default;
            if ((_1342_fieldType).IsObjectOrPointer()) {
              _1348_default = (_1342_fieldType).ToNullExpr();
            }
            _1339_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1339_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1343_fieldRustName, _1348_default)));
          }
        }
      }
      BigInteger _hi9 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1349_typeParamI = BigInteger.Zero; _1349_typeParamI < _hi9; _1349_typeParamI++) {
        DAST._IType _1350_typeArg;
        RAST._ITypeParamDecl _1351_typeParam;
        DAST._IType _out34;
        RAST._ITypeParamDecl _out35;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1349_typeParamI), out _out34, out _out35);
        _1350_typeArg = _out34;
        _1351_typeParam = _out35;
        RAST._IType _1352_rTypeArg;
        RAST._IType _out36;
        _out36 = (this).GenType(_1350_typeArg, DCOMP.GenTypeContext.@default());
        _1352_rTypeArg = _out36;
        _1338_fields = Dafny.Sequence<RAST._IField>.Concat(_1338_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1349_typeParamI)), RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1352_rTypeArg))))));
        _1339_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1339_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1349_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      DCOMP._IExternAttribute _1353_extern;
      _1353_extern = DCOMP.__default.ExtractExtern((c).dtor_attributes, (c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _1354_className = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((_1353_extern).is_SimpleExtern) {
        _1354_className = (_1353_extern).dtor_overrideName;
      } else {
        _1354_className = DCOMP.__default.escapeName((c).dtor_name);
        if ((_1353_extern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multi-argument externs not supported for classes yet"));
        }
      }
      RAST._IStruct _1355_struct;
      _1355_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1354_className, _1335_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1338_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_1353_extern).is_NoExtern) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1355_struct)));
      }
      Dafny.ISequence<RAST._IImplMember> _1356_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1357_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out37;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out38;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1333_typeParamsSeq, out _out37, out _out38);
      _1356_implBody = _out37;
      _1357_traitBodies = _out38;
      if (((_1353_extern).is_NoExtern) && (!(_1354_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default")))) {
        _1356_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.__default.SelfOwned)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel((this).allocate)).AsExpr()).ApplyType1(RAST.__default.SelfOwned)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1356_implBody);
      }
      RAST._IType _1358_selfTypeForImpl = RAST.Type.Default();
      if (((_1353_extern).is_NoExtern) || ((_1353_extern).is_UnsupportedExtern)) {
        _1358_selfTypeForImpl = RAST.Type.create_TIdentifier(_1354_className);
      } else if ((_1353_extern).is_AdvancedExtern) {
        _1358_selfTypeForImpl = (((RAST.__default.crate).MSel((_1353_extern).dtor_enclosingModule)).MSel((_1353_extern).dtor_overrideName)).AsType();
      } else if ((_1353_extern).is_SimpleExtern) {
        _1358_selfTypeForImpl = RAST.Type.create_TIdentifier((_1353_extern).dtor_overrideName);
      }
      if ((new BigInteger((_1356_implBody).Count)).Sign == 1) {
        RAST._IImpl _1359_i;
        _1359_i = RAST.Impl.create_Impl(_1335_rTypeParamsDecls, RAST.Type.create_TypeApp(_1358_selfTypeForImpl, _1334_rTypeParams), _1336_whereConstraints, _1356_implBody);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1359_i)));
      }
      RAST._IType _1360_genSelfPath;
      RAST._IType _out39;
      _out39 = DCOMP.COMP.GenPathType(path);
      _1360_genSelfPath = _out39;
      if (!(_1354_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1335_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(RAST.__default.AnyTrait))), RAST.Type.create_TypeApp(_1360_genSelfPath, _1334_rTypeParams), _1336_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(RAST.__default.AnyTrait)))))))));
      }
      Dafny.ISequence<DAST._IType> _1361_superClasses;
      _1361_superClasses = (((_1354_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) ? (Dafny.Sequence<DAST._IType>.FromElements()) : ((c).dtor_superClasses));
      BigInteger _hi10 = new BigInteger((_1361_superClasses).Count);
      for (BigInteger _1362_i = BigInteger.Zero; _1362_i < _hi10; _1362_i++) {
        DAST._IType _1363_superClass;
        _1363_superClass = (_1361_superClasses).Select(_1362_i);
        DAST._IType _source70 = _1363_superClass;
        bool unmatched70 = true;
        if (unmatched70) {
          if (_source70.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source70.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1364_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1365_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1366_properMethods = resolved0.dtor_properMethods;
              unmatched70 = false;
              {
                RAST._IType _1367_pathStr;
                RAST._IType _out40;
                _out40 = DCOMP.COMP.GenPathType(_1364_traitPath);
                _1367_pathStr = _out40;
                Dafny.ISequence<RAST._IType> _1368_typeArgs;
                Dafny.ISequence<RAST._IType> _out41;
                _out41 = (this).GenTypeArgs(_1365_typeArgs, DCOMP.GenTypeContext.@default());
                _1368_typeArgs = _out41;
                Dafny.ISequence<RAST._IImplMember> _1369_body;
                _1369_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1357_traitBodies).Contains(_1364_traitPath)) {
                  _1369_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1357_traitBodies,_1364_traitPath);
                }
                RAST._IType _1370_traitType;
                _1370_traitType = RAST.Type.create_TypeApp(_1367_pathStr, _1368_typeArgs);
                if (!((_1353_extern).is_NoExtern)) {
                  if (((new BigInteger((_1369_body).Count)).Sign == 0) && ((new BigInteger((_1366_properMethods).Count)).Sign != 0)) {
                    goto continue_0;
                  }
                  if ((new BigInteger((_1369_body).Count)) != (new BigInteger((_1366_properMethods).Count))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: In the class "), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(path, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1371_s) => {
  return ((_1371_s));
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", some proper methods of ")), (_1370_traitType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" are marked {:extern} and some are not.")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" For the Rust compiler, please make all methods (")), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_1366_properMethods, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1372_s) => {
  return (_1372_s);
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")  bodiless and mark as {:extern} and implement them in a Rust file, ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("or mark none of them as {:extern} and implement them in Dafny. ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.")));
                  }
                }
                RAST._IModDecl _1373_x;
                _1373_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1335_rTypeParamsDecls, _1370_traitType, RAST.Type.create_TypeApp(_1360_genSelfPath, _1334_rTypeParams), _1336_whereConstraints, _1369_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1373_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1335_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1370_traitType))), RAST.Type.create_TypeApp(_1360_genSelfPath, _1334_rTypeParams), _1336_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1370_traitType)))))))));
              }
            }
          }
        }
        if (unmatched70) {
          unmatched70 = false;
        }
      continue_0: ;
      }
    after_0: ;
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1374_typeParamsSeq;
      _1374_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1375_typeParamDecls;
      _1375_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1376_typeParams;
      _1376_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi11 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1377_tpI = BigInteger.Zero; _1377_tpI < _hi11; _1377_tpI++) {
          DAST._ITypeArgDecl _1378_tp;
          _1378_tp = ((t).dtor_typeParams).Select(_1377_tpI);
          DAST._IType _1379_typeArg;
          RAST._ITypeParamDecl _1380_typeParamDecl;
          DAST._IType _out42;
          RAST._ITypeParamDecl _out43;
          (this).GenTypeParam(_1378_tp, out _out42, out _out43);
          _1379_typeArg = _out42;
          _1380_typeParamDecl = _out43;
          _1374_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1374_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1379_typeArg));
          _1375_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1375_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1380_typeParamDecl));
          RAST._IType _1381_typeParam;
          RAST._IType _out44;
          _out44 = (this).GenType(_1379_typeArg, DCOMP.GenTypeContext.@default());
          _1381_typeParam = _out44;
          _1376_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1376_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1381_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1382_fullPath;
      _1382_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1383_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1384___v56;
      Dafny.ISequence<RAST._IImplMember> _out45;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out46;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1382_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1374_typeParamsSeq, out _out45, out _out46);
      _1383_implBody = _out45;
      _1384___v56 = _out46;
      Dafny.ISequence<RAST._IType> _1385_parents;
      _1385_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi12 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1386_i = BigInteger.Zero; _1386_i < _hi12; _1386_i++) {
        RAST._IType _1387_tpe;
        RAST._IType _out47;
        _out47 = (this).GenType(((t).dtor_parents).Select(_1386_i), DCOMP.GenTypeContext.ForTraitParents());
        _1387_tpe = _out47;
        _1385_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1385_parents, Dafny.Sequence<RAST._IType>.FromElements(_1387_tpe)), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply1(RAST.Type.create_DynType(_1387_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1375_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1376_typeParams), _1385_parents, _1383_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1388_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1389_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1390_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1391_whereConstraints;
      Dafny.ISequence<DAST._IType> _out48;
      Dafny.ISequence<RAST._IType> _out49;
      Dafny.ISequence<RAST._ITypeParamDecl> _out50;
      Dafny.ISequence<Dafny.Rune> _out51;
      (this).GenTypeParameters((c).dtor_typeParams, out _out48, out _out49, out _out50, out _out51);
      _1388_typeParamsSeq = _out48;
      _1389_rTypeParams = _out49;
      _1390_rTypeParamsDecls = _out50;
      _1391_whereConstraints = _out51;
      Dafny.ISequence<Dafny.Rune> _1392_constrainedTypeParams;
      _1392_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1390_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1393_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source71 = DCOMP.COMP.NewtypeRangeToRustType((c).dtor_range);
      bool unmatched71 = true;
      if (unmatched71) {
        if (_source71.is_Some) {
          RAST._IType _1394_v = _source71.dtor_value;
          unmatched71 = false;
          _1393_underlyingType = _1394_v;
        }
      }
      if (unmatched71) {
        unmatched71 = false;
        RAST._IType _out52;
        _out52 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1393_underlyingType = _out52;
      }
      DAST._IType _1395_resultingType;
      _1395_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1396_newtypeName;
      _1396_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1396_newtypeName, _1390_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1393_underlyingType))))));
      RAST._IExpr _1397_fnBody;
      _1397_fnBody = RAST.Expr.create_Identifier(_1396_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source72 = (c).dtor_witnessExpr;
      bool unmatched72 = true;
      if (unmatched72) {
        if (_source72.is_Some) {
          DAST._IExpression _1398_e = _source72.dtor_value;
          unmatched72 = false;
          {
            DAST._IExpression _1399_e;
            _1399_e = ((object.Equals((c).dtor_base, _1395_resultingType)) ? (_1398_e) : (DAST.Expression.create_Convert(_1398_e, (c).dtor_base, _1395_resultingType)));
            RAST._IExpr _1400_eStr;
            DCOMP._IOwnership _1401___v57;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1402___v58;
            RAST._IExpr _out53;
            DCOMP._IOwnership _out54;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out55;
            (this).GenExpr(_1399_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out53, out _out54, out _out55);
            _1400_eStr = _out53;
            _1401___v57 = _out54;
            _1402___v58 = _out55;
            _1397_fnBody = (_1397_fnBody).Apply1(_1400_eStr);
          }
        }
      }
      if (unmatched72) {
        unmatched72 = false;
        {
          _1397_fnBody = (_1397_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1403_body;
      _1403_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1397_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source73 = (c).dtor_constraint;
      bool unmatched73 = true;
      if (unmatched73) {
        if (_source73.is_None) {
          unmatched73 = false;
        }
      }
      if (unmatched73) {
        DAST._INewtypeConstraint value8 = _source73.dtor_value;
        DAST._IFormal _1404_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1405_constraintStmts = value8.dtor_constraintStmts;
        unmatched73 = false;
        RAST._IExpr _1406_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1407___v59;
        DCOMP._IEnvironment _1408_newEnv;
        RAST._IExpr _out56;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out57;
        DCOMP._IEnvironment _out58;
        (this).GenStmts(_1405_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out56, out _out57, out _out58);
        _1406_rStmts = _out56;
        _1407___v59 = _out57;
        _1408_newEnv = _out58;
        Dafny.ISequence<RAST._IFormal> _1409_rFormals;
        Dafny.ISequence<RAST._IFormal> _out59;
        _out59 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1404_formal), false);
        _1409_rFormals = _out59;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1390_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1396_newtypeName), _1389_rTypeParams), _1391_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1409_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1406_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1390_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1396_newtypeName), _1389_rTypeParams), _1391_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1403_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1390_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1396_newtypeName), _1389_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1390_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1396_newtypeName), _1389_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1393_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(((RAST.Path.create_Self()).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))).AsType())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1410_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1411_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1412_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1413_whereConstraints;
      Dafny.ISequence<DAST._IType> _out60;
      Dafny.ISequence<RAST._IType> _out61;
      Dafny.ISequence<RAST._ITypeParamDecl> _out62;
      Dafny.ISequence<Dafny.Rune> _out63;
      (this).GenTypeParameters((c).dtor_typeParams, out _out60, out _out61, out _out62, out _out63);
      _1410_typeParamsSeq = _out60;
      _1411_rTypeParams = _out61;
      _1412_rTypeParamsDecls = _out62;
      _1413_whereConstraints = _out63;
      Dafny.ISequence<Dafny.Rune> _1414_synonymTypeName;
      _1414_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1415_resultingType;
      RAST._IType _out64;
      _out64 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1415_resultingType = _out64;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1414_synonymTypeName, _1412_rTypeParamsDecls, _1415_resultingType)));
      Dafny.ISequence<RAST._ITypeParamDecl> _1416_defaultConstrainedTypeParams;
      _1416_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1412_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Std.Wrappers._IOption<DAST._IExpression> _source74 = (c).dtor_witnessExpr;
      bool unmatched74 = true;
      if (unmatched74) {
        if (_source74.is_Some) {
          DAST._IExpression _1417_e = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IExpr _1418_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1419___v60;
            DCOMP._IEnvironment _1420_newEnv;
            RAST._IExpr _out65;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out66;
            DCOMP._IEnvironment _out67;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out65, out _out66, out _out67);
            _1418_rStmts = _out65;
            _1419___v60 = _out66;
            _1420_newEnv = _out67;
            RAST._IExpr _1421_rExpr;
            DCOMP._IOwnership _1422___v61;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1423___v62;
            RAST._IExpr _out68;
            DCOMP._IOwnership _out69;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out70;
            (this).GenExpr(_1417_e, DCOMP.SelfInfo.create_NoSelf(), _1420_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out68, out _out69, out _out70);
            _1421_rExpr = _out68;
            _1422___v61 = _out69;
            _1423___v62 = _out70;
            Dafny.ISequence<Dafny.Rune> _1424_constantName;
            _1424_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1424_constantName, _1416_defaultConstrainedTypeParams, Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1415_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1418_rStmts).Then(_1421_rExpr)))))));
          }
        }
      }
      if (unmatched74) {
        unmatched74 = false;
      }
      return s;
    }
    public bool TypeIsEq(DAST._IType t) {
      DAST._IType _source75 = t;
      bool unmatched75 = true;
      if (unmatched75) {
        if (_source75.is_UserDefined) {
          unmatched75 = false;
          return true;
        }
      }
      if (unmatched75) {
        if (_source75.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1425_ts = _source75.dtor_Tuple_a0;
          unmatched75 = false;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1426_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1426_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1427_t = (DAST._IType)_forall_var_5;
            return !((_1426_ts).Contains(_1427_t)) || ((this).TypeIsEq(_1427_t));
          }))))(_1425_ts);
        }
      }
      if (unmatched75) {
        if (_source75.is_Array) {
          DAST._IType _1428_t = _source75.dtor_element;
          unmatched75 = false;
          return (this).TypeIsEq(_1428_t);
        }
      }
      if (unmatched75) {
        if (_source75.is_Seq) {
          DAST._IType _1429_t = _source75.dtor_element;
          unmatched75 = false;
          return (this).TypeIsEq(_1429_t);
        }
      }
      if (unmatched75) {
        if (_source75.is_Set) {
          DAST._IType _1430_t = _source75.dtor_element;
          unmatched75 = false;
          return (this).TypeIsEq(_1430_t);
        }
      }
      if (unmatched75) {
        if (_source75.is_Multiset) {
          DAST._IType _1431_t = _source75.dtor_element;
          unmatched75 = false;
          return (this).TypeIsEq(_1431_t);
        }
      }
      if (unmatched75) {
        if (_source75.is_Map) {
          DAST._IType _1432_k = _source75.dtor_key;
          DAST._IType _1433_v = _source75.dtor_value;
          unmatched75 = false;
          return ((this).TypeIsEq(_1432_k)) && ((this).TypeIsEq(_1433_v));
        }
      }
      if (unmatched75) {
        if (_source75.is_SetBuilder) {
          DAST._IType _1434_t = _source75.dtor_element;
          unmatched75 = false;
          return (this).TypeIsEq(_1434_t);
        }
      }
      if (unmatched75) {
        if (_source75.is_MapBuilder) {
          DAST._IType _1435_k = _source75.dtor_key;
          DAST._IType _1436_v = _source75.dtor_value;
          unmatched75 = false;
          return ((this).TypeIsEq(_1435_k)) && ((this).TypeIsEq(_1436_v));
        }
      }
      if (unmatched75) {
        if (_source75.is_Arrow) {
          unmatched75 = false;
          return false;
        }
      }
      if (unmatched75) {
        if (_source75.is_Primitive) {
          unmatched75 = false;
          return true;
        }
      }
      if (unmatched75) {
        if (_source75.is_Passthrough) {
          unmatched75 = false;
          return true;
        }
      }
      if (unmatched75) {
        if (_source75.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _1437_i = _source75.dtor_TypeArg_a0;
          unmatched75 = false;
          return true;
        }
      }
      if (unmatched75) {
        unmatched75 = false;
        return true;
      }
      throw new System.Exception("unexpected control point");
    }
    public bool DatatypeIsEq(DAST._IDatatype c) {
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1438_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1438_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1439_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1439_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1440_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1438_c).dtor_ctors).Contains(_1439_ctor)) && (((_1439_ctor).dtor_args).Contains(_1440_arg))) || ((this).TypeIsEq(((_1440_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1441_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1442_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1443_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1444_whereConstraints;
      Dafny.ISequence<DAST._IType> _out71;
      Dafny.ISequence<RAST._IType> _out72;
      Dafny.ISequence<RAST._ITypeParamDecl> _out73;
      Dafny.ISequence<Dafny.Rune> _out74;
      (this).GenTypeParameters((c).dtor_typeParams, out _out71, out _out72, out _out73, out _out74);
      _1441_typeParamsSeq = _out71;
      _1442_rTypeParams = _out72;
      _1443_rTypeParamsDecls = _out73;
      _1444_whereConstraints = _out74;
      Dafny.ISequence<Dafny.Rune> _1445_datatypeName;
      _1445_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1446_ctors;
      _1446_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _1447_variances;
      _1447_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_1448_typeParamDecl) => {
        return (_1448_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1449_i = BigInteger.Zero; _1449_i < _hi13; _1449_i++) {
        DAST._IDatatypeCtor _1450_ctor;
        _1450_ctor = ((c).dtor_ctors).Select(_1449_i);
        Dafny.ISequence<RAST._IField> _1451_ctorArgs;
        _1451_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1452_isNumeric;
        _1452_isNumeric = false;
        BigInteger _hi14 = new BigInteger(((_1450_ctor).dtor_args).Count);
        for (BigInteger _1453_j = BigInteger.Zero; _1453_j < _hi14; _1453_j++) {
          DAST._IDatatypeDtor _1454_dtor;
          _1454_dtor = ((_1450_ctor).dtor_args).Select(_1453_j);
          RAST._IType _1455_formalType;
          RAST._IType _out75;
          _out75 = (this).GenType(((_1454_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1455_formalType = _out75;
          Dafny.ISequence<Dafny.Rune> _1456_formalName;
          _1456_formalName = DCOMP.__default.escapeVar(((_1454_dtor).dtor_formal).dtor_name);
          if (((_1453_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1456_formalName))) {
            _1452_isNumeric = true;
          }
          if ((((_1453_j).Sign != 0) && (_1452_isNumeric)) && (!(Std.Strings.__default.OfNat(_1453_j)).Equals(_1456_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1456_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1453_j)));
            _1452_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1451_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1451_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1456_formalName, RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1455_formalType))))));
          } else {
            _1451_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1451_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1456_formalName, _1455_formalType))));
          }
        }
        RAST._IFields _1457_namedFields;
        _1457_namedFields = RAST.Fields.create_NamedFields(_1451_ctorArgs);
        if (_1452_isNumeric) {
          _1457_namedFields = (_1457_namedFields).ToNamelessFields();
        }
        _1446_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1446_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1450_ctor).dtor_name), _1457_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1458_selfPath;
      _1458_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1459_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1460_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out76;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out77;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1458_selfPath, _1441_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1447_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1441_typeParamsSeq, out _out76, out _out77);
      _1459_implBodyRaw = _out76;
      _1460_traitBodies = _out77;
      Dafny.ISequence<RAST._IImplMember> _1461_implBody;
      _1461_implBody = _1459_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1462_emittedFields;
      _1462_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi15 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1463_i = BigInteger.Zero; _1463_i < _hi15; _1463_i++) {
        DAST._IDatatypeCtor _1464_ctor;
        _1464_ctor = ((c).dtor_ctors).Select(_1463_i);
        BigInteger _hi16 = new BigInteger(((_1464_ctor).dtor_args).Count);
        for (BigInteger _1465_j = BigInteger.Zero; _1465_j < _hi16; _1465_j++) {
          DAST._IDatatypeDtor _1466_dtor;
          _1466_dtor = ((_1464_ctor).dtor_args).Select(_1465_j);
          Dafny.ISequence<Dafny.Rune> _1467_callName;
          _1467_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1466_dtor).dtor_callName, DCOMP.__default.escapeVar(((_1466_dtor).dtor_formal).dtor_name));
          if (!((_1462_emittedFields).Contains(_1467_callName))) {
            _1462_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1462_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1467_callName));
            RAST._IType _1468_formalType;
            RAST._IType _out78;
            _out78 = (this).GenType(((_1466_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1468_formalType = _out78;
            Dafny.ISequence<RAST._IMatchCase> _1469_cases;
            _1469_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi17 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1470_k = BigInteger.Zero; _1470_k < _hi17; _1470_k++) {
              DAST._IDatatypeCtor _1471_ctor2;
              _1471_ctor2 = ((c).dtor_ctors).Select(_1470_k);
              Dafny.ISequence<Dafny.Rune> _1472_pattern;
              _1472_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1445_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1471_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1473_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1474_hasMatchingField;
              _1474_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1475_patternInner;
              _1475_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1476_isNumeric;
              _1476_isNumeric = false;
              BigInteger _hi18 = new BigInteger(((_1471_ctor2).dtor_args).Count);
              for (BigInteger _1477_l = BigInteger.Zero; _1477_l < _hi18; _1477_l++) {
                DAST._IDatatypeDtor _1478_dtor2;
                _1478_dtor2 = ((_1471_ctor2).dtor_args).Select(_1477_l);
                Dafny.ISequence<Dafny.Rune> _1479_patternName;
                _1479_patternName = DCOMP.__default.escapeVar(((_1478_dtor2).dtor_formal).dtor_name);
                if (((_1477_l).Sign == 0) && ((_1479_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1476_isNumeric = true;
                }
                if (_1476_isNumeric) {
                  _1479_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1478_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1477_l)));
                }
                if (object.Equals(((_1466_dtor).dtor_formal).dtor_name, ((_1478_dtor2).dtor_formal).dtor_name)) {
                  _1474_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1479_patternName);
                }
                _1475_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1475_patternInner, _1479_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1476_isNumeric) {
                _1472_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1472_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1475_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1472_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1472_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1475_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1474_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1473_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1474_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1473_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1474_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1473_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _1480_ctorMatch;
              _1480_ctorMatch = RAST.MatchCase.create(_1472_pattern, RAST.Expr.create_RawExpr(_1473_rhs));
              _1469_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1469_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1480_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1469_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1469_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1445_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _1481_methodBody;
            _1481_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1469_cases);
            _1461_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1461_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1467_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1468_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1481_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1482_coerceTypes;
      _1482_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1483_rCoerceTypeParams;
      _1483_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1484_coerceArguments;
      _1484_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1485_coerceMap;
      _1485_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1486_rCoerceMap;
      _1486_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1487_coerceMapToArg;
      _1487_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1488_types;
        _1488_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi19 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1489_typeI = BigInteger.Zero; _1489_typeI < _hi19; _1489_typeI++) {
          DAST._ITypeArgDecl _1490_typeParam;
          _1490_typeParam = ((c).dtor_typeParams).Select(_1489_typeI);
          DAST._IType _1491_typeArg;
          RAST._ITypeParamDecl _1492_rTypeParamDecl;
          DAST._IType _out79;
          RAST._ITypeParamDecl _out80;
          (this).GenTypeParam(_1490_typeParam, out _out79, out _out80);
          _1491_typeArg = _out79;
          _1492_rTypeParamDecl = _out80;
          RAST._IType _1493_rTypeArg;
          RAST._IType _out81;
          _out81 = (this).GenType(_1491_typeArg, DCOMP.GenTypeContext.@default());
          _1493_rTypeArg = _out81;
          _1488_types = Dafny.Sequence<RAST._IType>.Concat(_1488_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1493_rTypeArg))));
          if (((_1489_typeI) < (new BigInteger((_1447_variances).Count))) && (((_1447_variances).Select(_1489_typeI)).is_Nonvariant)) {
            _1482_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1482_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1493_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1494_coerceTypeParam;
          _1494_coerceTypeParam = Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_1490_typeParam, _pat_let20_0 => Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_pat_let20_0, _1495_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1489_typeI)), _pat_let21_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(_pat_let21_0, _1496_dt__update_hname_h0 => DAST.TypeArgDecl.create(_1496_dt__update_hname_h0, (_1495_dt__update__tmp_h0).dtor_bounds, (_1495_dt__update__tmp_h0).dtor_variance)))));
          DAST._IType _1497_coerceTypeArg;
          RAST._ITypeParamDecl _1498_rCoerceTypeParamDecl;
          DAST._IType _out82;
          RAST._ITypeParamDecl _out83;
          (this).GenTypeParam(_1494_coerceTypeParam, out _out82, out _out83);
          _1497_coerceTypeArg = _out82;
          _1498_rCoerceTypeParamDecl = _out83;
          _1485_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1485_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1491_typeArg, _1497_coerceTypeArg)));
          RAST._IType _1499_rCoerceType;
          RAST._IType _out84;
          _out84 = (this).GenType(_1497_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1499_rCoerceType = _out84;
          _1486_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1486_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1493_rTypeArg, _1499_rCoerceType)));
          _1482_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1482_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1499_rCoerceType));
          _1483_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1483_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1498_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1500_coerceFormal;
          _1500_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1489_typeI));
          _1487_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1487_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1493_rTypeArg, _1499_rCoerceType), (RAST.Expr.create_Identifier(_1500_coerceFormal)).Clone())));
          _1484_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1484_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1500_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1493_rTypeArg), _1499_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        _1446_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1446_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1501_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1501_tpe);
})), _1488_types)))));
      }
      bool _1502_cIsEq;
      _1502_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1502_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1445_datatypeName, _1443_rTypeParamsDecls, _1446_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1443_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1445_datatypeName), _1442_rTypeParams), _1444_whereConstraints, _1461_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1503_printImplBodyCases;
      _1503_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1504_hashImplBodyCases;
      _1504_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1505_coerceImplBodyCases;
      _1505_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi20 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1506_i = BigInteger.Zero; _1506_i < _hi20; _1506_i++) {
        DAST._IDatatypeCtor _1507_ctor;
        _1507_ctor = ((c).dtor_ctors).Select(_1506_i);
        Dafny.ISequence<Dafny.Rune> _1508_ctorMatch;
        _1508_ctorMatch = DCOMP.__default.escapeName((_1507_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1509_modulePrefix;
        _1509_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1510_ctorName;
        _1510_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1509_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1507_ctor).dtor_name));
        if (((new BigInteger((_1510_ctorName).Count)) >= (new BigInteger(13))) && (((_1510_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1510_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1511_printRhs;
        _1511_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1510_ctorName), (((_1507_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1512_hashRhs;
        _1512_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1513_coerceRhsArgs;
        _1513_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1514_isNumeric;
        _1514_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1515_ctorMatchInner;
        _1515_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi21 = new BigInteger(((_1507_ctor).dtor_args).Count);
        for (BigInteger _1516_j = BigInteger.Zero; _1516_j < _hi21; _1516_j++) {
          DAST._IDatatypeDtor _1517_dtor;
          _1517_dtor = ((_1507_ctor).dtor_args).Select(_1516_j);
          Dafny.ISequence<Dafny.Rune> _1518_patternName;
          _1518_patternName = DCOMP.__default.escapeVar(((_1517_dtor).dtor_formal).dtor_name);
          DAST._IType _1519_formalType;
          _1519_formalType = ((_1517_dtor).dtor_formal).dtor_typ;
          if (((_1516_j).Sign == 0) && ((_1518_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1514_isNumeric = true;
          }
          if (_1514_isNumeric) {
            _1518_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1517_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1516_j)));
          }
          _1512_hashRhs = (((_1519_formalType).is_Arrow) ? ((_1512_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))) : ((_1512_hashRhs).Then((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1518_patternName), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state")))))));
          _1515_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1515_ctorMatchInner, _1518_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1516_j).Sign == 1) {
            _1511_printRhs = (_1511_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1511_printRhs = (_1511_printRhs).Then(RAST.Expr.create_RawExpr((((_1519_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1518_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1520_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1521_formalTpe;
          RAST._IType _out85;
          _out85 = (this).GenType(_1519_formalType, DCOMP.GenTypeContext.@default());
          _1521_formalTpe = _out85;
          DAST._IType _1522_newFormalType;
          _1522_newFormalType = (_1519_formalType).Replace(_1485_coerceMap);
          RAST._IType _1523_newFormalTpe;
          _1523_newFormalTpe = (_1521_formalTpe).ReplaceMap(_1486_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1524_upcastConverter;
          _1524_upcastConverter = (this).UpcastConversionLambda(_1519_formalType, _1521_formalTpe, _1522_newFormalType, _1523_newFormalTpe, _1487_coerceMapToArg);
          if ((_1524_upcastConverter).is_Success) {
            RAST._IExpr _1525_coercionFunction;
            _1525_coercionFunction = (_1524_upcastConverter).dtor_value;
            _1520_coerceRhsArg = (_1525_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1518_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1516_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1445_datatypeName));
            _1520_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1513_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1513_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1518_patternName, _1520_coerceRhsArg)));
        }
        RAST._IExpr _1526_coerceRhs;
        _1526_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1445_datatypeName)).FSel(DCOMP.__default.escapeName((_1507_ctor).dtor_name)), _1513_coerceRhsArgs);
        if (_1514_isNumeric) {
          _1508_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1508_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1515_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1508_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1508_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1515_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1507_ctor).dtor_hasAnyArgs) {
          _1511_printRhs = (_1511_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1511_printRhs = (_1511_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1503_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1503_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1445_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1508_ctorMatch), RAST.Expr.create_Block(_1511_printRhs))));
        _1504_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1504_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1445_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1508_ctorMatch), RAST.Expr.create_Block(_1512_hashRhs))));
        _1505_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1505_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1445_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1508_ctorMatch), RAST.Expr.create_Block(_1526_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1527_extraCases;
        _1527_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1445_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _1503_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1503_printImplBodyCases, _1527_extraCases);
        _1504_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1504_hashImplBodyCases, _1527_extraCases);
        _1505_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1505_coerceImplBodyCases, _1527_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1528_defaultConstrainedTypeParams;
      _1528_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1443_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1529_rTypeParamsDeclsWithEq;
      _1529_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1443_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1530_rTypeParamsDeclsWithHash;
      _1530_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1443_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1531_printImplBody;
      _1531_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1503_printImplBodyCases);
      RAST._IExpr _1532_hashImplBody;
      _1532_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1504_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1443_rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug"))).AsType(), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1445_datatypeName), _1442_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType()))), Std.Wrappers.Option<RAST._IType>.create_Some((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Result"))).AsType()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1443_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1445_datatypeName), _1442_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType())), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1531_printImplBody))))))));
      if ((new BigInteger((_1483_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1533_coerceImplBody;
        _1533_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1505_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1443_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1445_datatypeName), _1442_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1483_rCoerceTypeParams, _1484_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1445_datatypeName), _1442_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1445_datatypeName), _1482_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.__default.SelfOwned)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1445_datatypeName), _1482_coerceTypes)), _1533_coerceImplBody))))))))));
      }
      if (_1502_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1529_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1445_datatypeName), _1442_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1530_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1445_datatypeName), _1442_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))).AsType()))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1532_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1534_structName;
        _1534_structName = (RAST.Expr.create_Identifier(_1445_datatypeName)).FSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1535_structAssignments;
        _1535_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi22 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1536_i = BigInteger.Zero; _1536_i < _hi22; _1536_i++) {
          DAST._IDatatypeDtor _1537_dtor;
          _1537_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1536_i);
          _1535_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1535_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(((_1537_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1538_defaultConstrainedTypeParams;
        _1538_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1443_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1539_fullType;
        _1539_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1445_datatypeName), _1442_rTypeParams);
        if (_1502_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1538_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1539_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1539_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1534_structName, _1535_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1443_rTypeParamsDecls, ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).AsType()).Apply1(_1539_fullType), RAST.Type.create_Borrowed(_1539_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        for (BigInteger _1540_i = BigInteger.Zero; _1540_i < _hi23; _1540_i++) {
          Dafny.ISequence<Dafny.Rune> _1541_name;
          _1541_name = ((p).Select(_1540_i));
          if (escape) {
            _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs55 = DafnyCompilerRustUtils.__default.DafnyNameToContainingPathAndName(_1541_name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1542_modules = _let_tmp_rhs55.dtor__0;
            Dafny.ISequence<Dafny.Rune> _1543_finalName = _let_tmp_rhs55.dtor__1;
            BigInteger _hi24 = new BigInteger((_1542_modules).Count);
            for (BigInteger _1544_j = BigInteger.Zero; _1544_j < _hi24; _1544_j++) {
              r = (r).MSel(DCOMP.__default.escapeName(((_1542_modules).Select(_1544_j))));
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1543_finalName));
          } else {
            r = (r).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1541_name)));
          }
        }
      }
      return r;
    }
    public static RAST._IType GenPathType(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IType t = RAST.Type.Default();
      RAST._IPath _1545_p;
      RAST._IPath _out86;
      _out86 = DCOMP.COMP.GenPath(p, true);
      _1545_p = _out86;
      t = (_1545_p).AsType();
      return t;
    }
    public static RAST._IExpr GenPathExpr(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p, bool escape)
    {
      RAST._IExpr e = RAST.Expr.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        e = RAST.__default.self;
        return e;
      }
      RAST._IPath _1546_p;
      RAST._IPath _out87;
      _out87 = DCOMP.COMP.GenPath(p, escape);
      _1546_p = _out87;
      e = (_1546_p).AsExpr();
      return e;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi25 = new BigInteger((args).Count);
      for (BigInteger _1547_i = BigInteger.Zero; _1547_i < _hi25; _1547_i++) {
        RAST._IType _1548_genTp;
        RAST._IType _out88;
        _out88 = (this).GenType((args).Select(_1547_i), genTypeContext);
        _1548_genTp = _out88;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1548_genTp));
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, DCOMP._IGenTypeContext genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source76 = c;
      bool unmatched76 = true;
      if (unmatched76) {
        if (_source76.is_UserDefined) {
          DAST._IResolvedType _1549_resolved = _source76.dtor_resolved;
          unmatched76 = false;
          {
            RAST._IType _1550_t;
            RAST._IType _out89;
            _out89 = DCOMP.COMP.GenPathType((_1549_resolved).dtor_path);
            _1550_t = _out89;
            Dafny.ISequence<RAST._IType> _1551_typeArgs;
            Dafny.ISequence<RAST._IType> _out90;
            _out90 = (this).GenTypeArgs((_1549_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let22_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let22_0, _1552_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let23_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let23_0, _1553_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1552_dt__update__tmp_h0).dtor_inBinding, (_1552_dt__update__tmp_h0).dtor_inFn, _1553_dt__update_hforTraitParents_h0))))));
            _1551_typeArgs = _out90;
            s = RAST.Type.create_TypeApp(_1550_t, _1551_typeArgs);
            DAST._IResolvedTypeBase _source77 = (_1549_resolved).dtor_kind;
            bool unmatched77 = true;
            if (unmatched77) {
              if (_source77.is_Class) {
                unmatched77 = false;
                {
                  s = (this).Object(s);
                }
              }
            }
            if (unmatched77) {
              if (_source77.is_Datatype) {
                unmatched77 = false;
                {
                  if ((this).IsRcWrapped((_1549_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched77) {
              if (_source77.is_Trait) {
                unmatched77 = false;
                {
                  if (((_1549_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = RAST.__default.AnyTrait;
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched77) {
              DAST._IType _1554_base = _source77.dtor_baseType;
              DAST._INewtypeRange _1555_range = _source77.dtor_range;
              bool _1556_erased = _source77.dtor_erase;
              unmatched77 = false;
              {
                if (_1556_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source78 = DCOMP.COMP.NewtypeRangeToRustType(_1555_range);
                  bool unmatched78 = true;
                  if (unmatched78) {
                    if (_source78.is_Some) {
                      RAST._IType _1557_v = _source78.dtor_value;
                      unmatched78 = false;
                      s = _1557_v;
                    }
                  }
                  if (unmatched78) {
                    unmatched78 = false;
                    RAST._IType _1558_underlying;
                    RAST._IType _out91;
                    _out91 = (this).GenType(_1554_base, DCOMP.GenTypeContext.@default());
                    _1558_underlying = _out91;
                    s = RAST.Type.create_TSynonym(s, _1558_underlying);
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Object) {
          unmatched76 = false;
          {
            s = RAST.__default.AnyTrait;
            if (!((genTypeContext).dtor_forTraitParents)) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1559_types = _source76.dtor_Tuple_a0;
          unmatched76 = false;
          {
            Dafny.ISequence<RAST._IType> _1560_args;
            _1560_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1561_i;
            _1561_i = BigInteger.Zero;
            while ((_1561_i) < (new BigInteger((_1559_types).Count))) {
              RAST._IType _1562_generated;
              RAST._IType _out92;
              _out92 = (this).GenType((_1559_types).Select(_1561_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let24_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let24_0, _1563_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let25_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let25_0, _1564_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1563_dt__update__tmp_h1).dtor_inBinding, (_1563_dt__update__tmp_h1).dtor_inFn, _1564_dt__update_hforTraitParents_h1))))));
              _1562_generated = _out92;
              _1560_args = Dafny.Sequence<RAST._IType>.Concat(_1560_args, Dafny.Sequence<RAST._IType>.FromElements(_1562_generated));
              _1561_i = (_1561_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1559_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1560_args)) : (RAST.__default.SystemTupleType(_1560_args)));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Array) {
          DAST._IType _1565_element = _source76.dtor_element;
          BigInteger _1566_dims = _source76.dtor_dims;
          unmatched76 = false;
          {
            if ((_1566_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1567_elem;
              RAST._IType _out93;
              _out93 = (this).GenType(_1565_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let26_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let26_0, _1568_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let27_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let27_0, _1569_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1568_dt__update__tmp_h2).dtor_inBinding, (_1568_dt__update__tmp_h2).dtor_inFn, _1569_dt__update_hforTraitParents_h2))))));
              _1567_elem = _out93;
              if ((_1566_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1567_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1570_n;
                _1570_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1566_dims));
                s = (((RAST.__default.dafny__runtime).MSel(_1570_n)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1567_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Seq) {
          DAST._IType _1571_element = _source76.dtor_element;
          unmatched76 = false;
          {
            RAST._IType _1572_elem;
            RAST._IType _out94;
            _out94 = (this).GenType(_1571_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let28_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let28_0, _1573_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let29_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let29_0, _1574_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1573_dt__update__tmp_h3).dtor_inBinding, (_1573_dt__update__tmp_h3).dtor_inFn, _1574_dt__update_hforTraitParents_h3))))));
            _1572_elem = _out94;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1572_elem));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Set) {
          DAST._IType _1575_element = _source76.dtor_element;
          unmatched76 = false;
          {
            RAST._IType _1576_elem;
            RAST._IType _out95;
            _out95 = (this).GenType(_1575_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let30_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let30_0, _1577_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let31_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let31_0, _1578_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1577_dt__update__tmp_h4).dtor_inBinding, (_1577_dt__update__tmp_h4).dtor_inFn, _1578_dt__update_hforTraitParents_h4))))));
            _1576_elem = _out95;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1576_elem));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Multiset) {
          DAST._IType _1579_element = _source76.dtor_element;
          unmatched76 = false;
          {
            RAST._IType _1580_elem;
            RAST._IType _out96;
            _out96 = (this).GenType(_1579_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let32_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let32_0, _1581_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let33_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let33_0, _1582_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1581_dt__update__tmp_h5).dtor_inBinding, (_1581_dt__update__tmp_h5).dtor_inFn, _1582_dt__update_hforTraitParents_h5))))));
            _1580_elem = _out96;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1580_elem));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Map) {
          DAST._IType _1583_key = _source76.dtor_key;
          DAST._IType _1584_value = _source76.dtor_value;
          unmatched76 = false;
          {
            RAST._IType _1585_keyType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1583_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let34_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let34_0, _1586_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let35_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let35_0, _1587_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1586_dt__update__tmp_h6).dtor_inBinding, (_1586_dt__update__tmp_h6).dtor_inFn, _1587_dt__update_hforTraitParents_h6))))));
            _1585_keyType = _out97;
            RAST._IType _1588_valueType;
            RAST._IType _out98;
            _out98 = (this).GenType(_1584_value, genTypeContext);
            _1588_valueType = _out98;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1585_keyType, _1588_valueType));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_MapBuilder) {
          DAST._IType _1589_key = _source76.dtor_key;
          DAST._IType _1590_value = _source76.dtor_value;
          unmatched76 = false;
          {
            RAST._IType _1591_keyType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1589_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let36_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let36_0, _1592_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let37_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let37_0, _1593_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1592_dt__update__tmp_h7).dtor_inBinding, (_1592_dt__update__tmp_h7).dtor_inFn, _1593_dt__update_hforTraitParents_h7))))));
            _1591_keyType = _out99;
            RAST._IType _1594_valueType;
            RAST._IType _out100;
            _out100 = (this).GenType(_1590_value, genTypeContext);
            _1594_valueType = _out100;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1591_keyType, _1594_valueType));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_SetBuilder) {
          DAST._IType _1595_elem = _source76.dtor_element;
          unmatched76 = false;
          {
            RAST._IType _1596_elemType;
            RAST._IType _out101;
            _out101 = (this).GenType(_1595_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let38_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let38_0, _1597_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let39_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let39_0, _1598_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1597_dt__update__tmp_h8).dtor_inBinding, (_1597_dt__update__tmp_h8).dtor_inFn, _1598_dt__update_hforTraitParents_h8))))));
            _1596_elemType = _out101;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1596_elemType));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1599_args = _source76.dtor_args;
          DAST._IType _1600_result = _source76.dtor_result;
          unmatched76 = false;
          {
            Dafny.ISequence<RAST._IType> _1601_argTypes;
            _1601_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1602_i;
            _1602_i = BigInteger.Zero;
            while ((_1602_i) < (new BigInteger((_1599_args).Count))) {
              RAST._IType _1603_generated;
              RAST._IType _out102;
              _out102 = (this).GenType((_1599_args).Select(_1602_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let40_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let40_0, _1604_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let41_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let41_0, _1605_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let42_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let42_0, _1606_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1604_dt__update__tmp_h9).dtor_inBinding, _1606_dt__update_hinFn_h0, _1605_dt__update_hforTraitParents_h9))))))));
              _1603_generated = _out102;
              _1601_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1601_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1603_generated)));
              _1602_i = (_1602_i) + (BigInteger.One);
            }
            RAST._IType _1607_resultType;
            RAST._IType _out103;
            _out103 = (this).GenType(_1600_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1607_resultType = _out103;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1601_argTypes, _1607_resultType)));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source76.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1608_name = _h90;
          unmatched76 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1608_name));
        }
      }
      if (unmatched76) {
        if (_source76.is_Primitive) {
          DAST._IPrimitive _1609_p = _source76.dtor_Primitive_a0;
          unmatched76 = false;
          {
            DAST._IPrimitive _source79 = _1609_p;
            bool unmatched79 = true;
            if (unmatched79) {
              if (_source79.is_Int) {
                unmatched79 = false;
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).AsType();
              }
            }
            if (unmatched79) {
              if (_source79.is_Real) {
                unmatched79 = false;
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"))).AsType();
              }
            }
            if (unmatched79) {
              if (_source79.is_String) {
                unmatched79 = false;
                s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType()));
              }
            }
            if (unmatched79) {
              if (_source79.is_Bool) {
                unmatched79 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched79) {
              unmatched79 = false;
              s = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType();
            }
          }
        }
      }
      if (unmatched76) {
        Dafny.ISequence<Dafny.Rune> _1610_v = _source76.dtor_Passthrough_a0;
        unmatched76 = false;
        s = RAST.__default.RawType(_1610_v);
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
      for (BigInteger _1611_i = BigInteger.Zero; _1611_i < _hi26; _1611_i++) {
        DAST._IMethod _source80 = (body).Select(_1611_i);
        bool unmatched80 = true;
        if (unmatched80) {
          DAST._IMethod _1612_m = _source80;
          unmatched80 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source81 = (_1612_m).dtor_overridingPath;
            bool unmatched81 = true;
            if (unmatched81) {
              if (_source81.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1613_p = _source81.dtor_value;
                unmatched81 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1614_existing;
                  _1614_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1613_p)) {
                    _1614_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1613_p);
                  }
                  if (((new BigInteger(((_1612_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1615_genMethod;
                  RAST._IImplMember _out104;
                  _out104 = (this).GenMethod(_1612_m, true, enclosingType, enclosingTypeParams);
                  _1615_genMethod = _out104;
                  _1614_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1614_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1615_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1613_p, _1614_existing)));
                }
              }
            }
            if (unmatched81) {
              unmatched81 = false;
              {
                RAST._IImplMember _1616_generated;
                RAST._IImplMember _out105;
                _out105 = (this).GenMethod(_1612_m, forTrait, enclosingType, enclosingTypeParams);
                _1616_generated = _out105;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1616_generated));
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
      for (BigInteger _1617_i = BigInteger.Zero; _1617_i < _hi27; _1617_i++) {
        DAST._IFormal _1618_param;
        _1618_param = (@params).Select(_1617_i);
        RAST._IType _1619_paramType;
        RAST._IType _out106;
        _out106 = (this).GenType((_1618_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1619_paramType = _out106;
        if (((!((_1619_paramType).CanReadWithoutClone())) || (forLambda)) && (!((_1618_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1619_paramType = RAST.Type.create_Borrowed(_1619_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeVar((_1618_param).dtor_name), _1619_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1620_params;
      Dafny.ISequence<RAST._IFormal> _out107;
      _out107 = (this).GenParams((m).dtor_params, false);
      _1620_params = _out107;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1621_paramNames;
      _1621_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1622_paramTypes;
      _1622_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1623_paramI = BigInteger.Zero; _1623_paramI < _hi28; _1623_paramI++) {
        DAST._IFormal _1624_dafny__formal;
        _1624_dafny__formal = ((m).dtor_params).Select(_1623_paramI);
        RAST._IFormal _1625_formal;
        _1625_formal = (_1620_params).Select(_1623_paramI);
        Dafny.ISequence<Dafny.Rune> _1626_name;
        _1626_name = (_1625_formal).dtor_name;
        _1621_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1621_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1626_name));
        _1622_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1622_paramTypes, _1626_name, (_1625_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1627_fnName;
      _1627_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1628_selfIdent;
      _1628_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1629_selfId;
        _1629_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1629_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv190 = enclosingTypeParams;
        var _pat_let_tv191 = enclosingType;
        DAST._IType _1630_instanceType;
        _1630_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source82 = enclosingType;
          bool unmatched82 = true;
          if (unmatched82) {
            if (_source82.is_UserDefined) {
              DAST._IResolvedType _1631_r = _source82.dtor_resolved;
              unmatched82 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1631_r, _pat_let43_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let43_0, _1632_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv190, _pat_let44_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let44_0, _1633_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1632_dt__update__tmp_h0).dtor_path, _1633_dt__update_htypeArgs_h0, (_1632_dt__update__tmp_h0).dtor_kind, (_1632_dt__update__tmp_h0).dtor_attributes, (_1632_dt__update__tmp_h0).dtor_properMethods, (_1632_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched82) {
            unmatched82 = false;
            return _pat_let_tv191;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1634_selfFormal;
          _1634_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1620_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1634_selfFormal), _1620_params);
        } else {
          RAST._IType _1635_tpe;
          RAST._IType _out108;
          _out108 = (this).GenType(_1630_instanceType, DCOMP.GenTypeContext.@default());
          _1635_tpe = _out108;
          if ((_1629_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            if (((this).ObjectType).is_RcMut) {
              _1635_tpe = RAST.Type.create_Borrowed(_1635_tpe);
            }
          } else if ((_1629_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1635_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1635_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1635_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _1635_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.__default.SelfOwned));
              } else {
                _1635_tpe = RAST.Type.create_Borrowed(RAST.__default.SelfOwned);
              }
            }
          }
          _1620_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1629_selfId, _1635_tpe)), _1620_params);
        }
        _1628_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1629_selfId, _1630_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1636_retTypeArgs;
      _1636_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1637_typeI;
      _1637_typeI = BigInteger.Zero;
      while ((_1637_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1638_typeExpr;
        RAST._IType _out109;
        _out109 = (this).GenType(((m).dtor_outTypes).Select(_1637_typeI), DCOMP.GenTypeContext.@default());
        _1638_typeExpr = _out109;
        _1636_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1636_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1638_typeExpr));
        _1637_typeI = (_1637_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1639_visibility;
      _1639_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1640_typeParamsFiltered;
      _1640_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi29 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1641_typeParamI = BigInteger.Zero; _1641_typeParamI < _hi29; _1641_typeParamI++) {
        DAST._ITypeArgDecl _1642_typeParam;
        _1642_typeParam = ((m).dtor_typeParams).Select(_1641_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1642_typeParam).dtor_name)))) {
          _1640_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1640_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1642_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1643_typeParams;
      _1643_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1640_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi30 = new BigInteger((_1640_typeParamsFiltered).Count);
        for (BigInteger _1644_i = BigInteger.Zero; _1644_i < _hi30; _1644_i++) {
          DAST._IType _1645_typeArg;
          RAST._ITypeParamDecl _1646_rTypeParamDecl;
          DAST._IType _out110;
          RAST._ITypeParamDecl _out111;
          (this).GenTypeParam((_1640_typeParamsFiltered).Select(_1644_i), out _out110, out _out111);
          _1645_typeArg = _out110;
          _1646_rTypeParamDecl = _out111;
          var _pat_let_tv192 = _1646_rTypeParamDecl;
          _1646_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1646_rTypeParamDecl, _pat_let45_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let45_0, _1647_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv192).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait)), _pat_let46_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let46_0, _1648_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1647_dt__update__tmp_h1).dtor_content, _1648_dt__update_hconstraints_h0)))));
          _1643_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1643_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1646_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1649_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1650_env = DCOMP.Environment.Default();
      RAST._IExpr _1651_preBody;
      _1651_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1652_preAssignNames;
      _1652_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1653_preAssignTypes;
      _1653_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1654_earlyReturn;
        _1654_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source83 = (m).dtor_outVars;
        bool unmatched83 = true;
        if (unmatched83) {
          if (_source83.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1655_outVars = _source83.dtor_value;
            unmatched83 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1654_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi31 = new BigInteger((_1655_outVars).Count);
                for (BigInteger _1656_outI = BigInteger.Zero; _1656_outI < _hi31; _1656_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1657_outVar;
                  _1657_outVar = (_1655_outVars).Select(_1656_outI);
                  Dafny.ISequence<Dafny.Rune> _1658_outName;
                  _1658_outName = DCOMP.__default.escapeVar(_1657_outVar);
                  Dafny.ISequence<Dafny.Rune> _1659_tracker__name;
                  _1659_tracker__name = DCOMP.__default.AddAssignedPrefix(_1658_outName);
                  _1652_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1652_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1659_tracker__name));
                  _1653_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1653_preAssignTypes, _1659_tracker__name, RAST.Type.create_Bool());
                  _1651_preBody = (_1651_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1659_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1660_tupleArgs;
                _1660_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi32 = new BigInteger((_1655_outVars).Count);
                for (BigInteger _1661_outI = BigInteger.Zero; _1661_outI < _hi32; _1661_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1662_outVar;
                  _1662_outVar = (_1655_outVars).Select(_1661_outI);
                  RAST._IType _1663_outType;
                  RAST._IType _out112;
                  _out112 = (this).GenType(((m).dtor_outTypes).Select(_1661_outI), DCOMP.GenTypeContext.@default());
                  _1663_outType = _out112;
                  Dafny.ISequence<Dafny.Rune> _1664_outName;
                  _1664_outName = DCOMP.__default.escapeVar(_1662_outVar);
                  _1621_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1621_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1664_outName));
                  RAST._IType _1665_outMaybeType;
                  _1665_outMaybeType = (((_1663_outType).CanReadWithoutClone()) ? (_1663_outType) : (RAST.__default.MaybePlaceboType(_1663_outType)));
                  _1622_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1622_paramTypes, _1664_outName, _1665_outMaybeType);
                  _1660_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1660_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1664_outName));
                }
                _1654_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_1660_tupleArgs);
              }
            }
          }
        }
        if (unmatched83) {
          unmatched83 = false;
        }
        _1650_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1652_preAssignNames, _1621_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1653_preAssignTypes, _1622_paramTypes));
        RAST._IExpr _1666_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1667___v71;
        DCOMP._IEnvironment _1668___v72;
        RAST._IExpr _out113;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out114;
        DCOMP._IEnvironment _out115;
        (this).GenStmts((m).dtor_body, _1628_selfIdent, _1650_env, true, _1654_earlyReturn, out _out113, out _out114, out _out115);
        _1666_body = _out113;
        _1667___v71 = _out114;
        _1668___v72 = _out115;
        _1649_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1651_preBody).Then(_1666_body));
      } else {
        _1650_env = DCOMP.Environment.create(_1621_paramNames, _1622_paramTypes);
        _1649_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1639_visibility, RAST.Fn.create(_1627_fnName, _1643_typeParams, _1620_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1636_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1636_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1636_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1649_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1669_declarations;
      _1669_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1670_i;
      _1670_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1671_stmts;
      _1671_stmts = stmts;
      while ((_1670_i) < (new BigInteger((_1671_stmts).Count))) {
        DAST._IStatement _1672_stmt;
        _1672_stmt = (_1671_stmts).Select(_1670_i);
        DAST._IStatement _source84 = _1672_stmt;
        bool unmatched84 = true;
        if (unmatched84) {
          if (_source84.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1673_name = _source84.dtor_name;
            DAST._IType _1674_optType = _source84.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source84.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched84 = false;
              if (((_1670_i) + (BigInteger.One)) < (new BigInteger((_1671_stmts).Count))) {
                DAST._IStatement _source85 = (_1671_stmts).Select((_1670_i) + (BigInteger.One));
                bool unmatched85 = true;
                if (unmatched85) {
                  if (_source85.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source85.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> _1675_name2 = lhs0.dtor_ident;
                      DAST._IExpression _1676_rhs = _source85.dtor_value;
                      unmatched85 = false;
                      if (object.Equals(_1675_name2, _1673_name)) {
                        _1671_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1671_stmts).Subsequence(BigInteger.Zero, _1670_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1673_name, _1674_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1676_rhs)))), (_1671_stmts).Drop((_1670_i) + (new BigInteger(2))));
                        _1672_stmt = (_1671_stmts).Select(_1670_i);
                      }
                    }
                  }
                }
                if (unmatched85) {
                  unmatched85 = false;
                }
              }
            }
          }
        }
        if (unmatched84) {
          unmatched84 = false;
        }
        RAST._IExpr _1677_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1678_recIdents;
        DCOMP._IEnvironment _1679_newEnv2;
        RAST._IExpr _out116;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
        DCOMP._IEnvironment _out118;
        (this).GenStmt(_1672_stmt, selfIdent, newEnv, (isLast) && ((_1670_i) == ((new BigInteger((_1671_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out116, out _out117, out _out118);
        _1677_stmtExpr = _out116;
        _1678_recIdents = _out117;
        _1679_newEnv2 = _out118;
        newEnv = _1679_newEnv2;
        DAST._IStatement _source86 = _1672_stmt;
        bool unmatched86 = true;
        if (unmatched86) {
          if (_source86.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1680_name = _source86.dtor_name;
            unmatched86 = false;
            {
              _1669_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1669_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_1680_name)));
            }
          }
        }
        if (unmatched86) {
          unmatched86 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1678_recIdents, _1669_declarations));
        generated = (generated).Then(_1677_stmtExpr);
        _1670_i = (_1670_i) + (BigInteger.One);
        if ((_1677_stmtExpr).is_Return) {
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
      DAST._IAssignLhs _source87 = lhs;
      bool unmatched87 = true;
      if (unmatched87) {
        if (_source87.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1681_id = _source87.dtor_ident;
          unmatched87 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1682_idRust;
            _1682_idRust = DCOMP.__default.escapeVar(_1681_id);
            if (((env).IsBorrowed(_1682_idRust)) || ((env).IsBorrowedMut(_1682_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1682_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1682_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1682_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Select) {
          DAST._IExpression _1683_on = _source87.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1684_field = _source87.dtor_field;
          unmatched87 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1685_fieldName;
            _1685_fieldName = DCOMP.__default.escapeVar(_1684_field);
            RAST._IExpr _1686_onExpr;
            DCOMP._IOwnership _1687_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1688_recIdents;
            RAST._IExpr _out119;
            DCOMP._IOwnership _out120;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
            (this).GenExpr(_1683_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out119, out _out120, out _out121);
            _1686_onExpr = _out119;
            _1687_onOwned = _out120;
            _1688_recIdents = _out121;
            RAST._IExpr _source88 = _1686_onExpr;
            bool unmatched88 = true;
            if (unmatched88) {
              bool disjunctiveMatch12 = false;
              if (_source88.is_Call) {
                RAST._IExpr obj2 = _source88.dtor_obj;
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
              if (_source88.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name6 = _source88.dtor_name;
                if (object.Equals(name6, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch12 = true;
                }
              }
              if (_source88.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op14 = _source88.dtor_op1;
                if (object.Equals(op14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying4 = _source88.dtor_underlying;
                  if (underlying4.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name7 = underlying4.dtor_name;
                    if (object.Equals(name7, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      disjunctiveMatch12 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch12) {
                unmatched88 = false;
                Dafny.ISequence<Dafny.Rune> _1689_isAssignedVar;
                _1689_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1685_fieldName);
                if (((newEnv).dtor_names).Contains(_1689_isAssignedVar)) {
                  generated = (((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1685_fieldName), RAST.Expr.create_Identifier(_1689_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1689_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1689_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1685_fieldName, rhs);
                }
              }
            }
            if (unmatched88) {
              unmatched88 = false;
              if (!object.Equals(_1686_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1686_onExpr = ((this).modify__macro).Apply1(_1686_onExpr);
              }
              generated = RAST.__default.AssignMember(_1686_onExpr, _1685_fieldName, rhs);
            }
            readIdents = _1688_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched87) {
        DAST._IExpression _1690_on = _source87.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1691_indices = _source87.dtor_indices;
        unmatched87 = false;
        {
          RAST._IExpr _1692_onExpr;
          DCOMP._IOwnership _1693_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1694_recIdents;
          RAST._IExpr _out122;
          DCOMP._IOwnership _out123;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
          (this).GenExpr(_1690_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out122, out _out123, out _out124);
          _1692_onExpr = _out122;
          _1693_onOwned = _out123;
          _1694_recIdents = _out124;
          readIdents = _1694_recIdents;
          _1692_onExpr = ((this).modify__macro).Apply1(_1692_onExpr);
          RAST._IExpr _1695_r;
          _1695_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1696_indicesExpr;
          _1696_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi33 = new BigInteger((_1691_indices).Count);
          for (BigInteger _1697_i = BigInteger.Zero; _1697_i < _hi33; _1697_i++) {
            RAST._IExpr _1698_idx;
            DCOMP._IOwnership _1699___v81;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1700_recIdentsIdx;
            RAST._IExpr _out125;
            DCOMP._IOwnership _out126;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out127;
            (this).GenExpr((_1691_indices).Select(_1697_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out125, out _out126, out _out127);
            _1698_idx = _out125;
            _1699___v81 = _out126;
            _1700_recIdentsIdx = _out127;
            Dafny.ISequence<Dafny.Rune> _1701_varName;
            _1701_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1697_i));
            _1696_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1696_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1701_varName)));
            _1695_r = (_1695_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1701_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1698_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1700_recIdentsIdx);
          }
          if ((new BigInteger((_1691_indices).Count)) > (BigInteger.One)) {
            _1692_onExpr = (_1692_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1702_rhs;
          _1702_rhs = rhs;
          var _pat_let_tv193 = env;
          if (((_1692_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1692_onExpr).LhsIdentifierName(), _pat_let47_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let47_0, _1703_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv193).GetType(_1703_name), _pat_let48_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let48_0, _1704_tpe => ((_1704_tpe).is_Some) && (((_1704_tpe).dtor_value).IsUninitArray())))))))) {
            _1702_rhs = RAST.__default.MaybeUninitNew(_1702_rhs);
          }
          generated = (_1695_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1692_onExpr, _1696_indicesExpr)), _1702_rhs));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source89 = stmt;
      bool unmatched89 = true;
      if (unmatched89) {
        if (_source89.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1705_fields = _source89.dtor_fields;
          unmatched89 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi34 = new BigInteger((_1705_fields).Count);
            for (BigInteger _1706_i = BigInteger.Zero; _1706_i < _hi34; _1706_i++) {
              DAST._IFormal _1707_field;
              _1707_field = (_1705_fields).Select(_1706_i);
              Dafny.ISequence<Dafny.Rune> _1708_fieldName;
              _1708_fieldName = DCOMP.__default.escapeVar((_1707_field).dtor_name);
              RAST._IType _1709_fieldTyp;
              RAST._IType _out128;
              _out128 = (this).GenType((_1707_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1709_fieldTyp = _out128;
              Dafny.ISequence<Dafny.Rune> _1710_isAssignedVar;
              _1710_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1708_fieldName);
              if (((newEnv).dtor_names).Contains(_1710_isAssignedVar)) {
                RAST._IExpr _1711_rhs;
                DCOMP._IOwnership _1712___v82;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1713___v83;
                RAST._IExpr _out129;
                DCOMP._IOwnership _out130;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1707_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out129, out _out130, out _out131);
                _1711_rhs = _out129;
                _1712___v82 = _out130;
                _1713___v83 = _out131;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1710_isAssignedVar));
                generated = (generated).Then((((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1708_fieldName), RAST.Expr.create_Identifier(_1710_isAssignedVar), _1711_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1710_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1714_name = _source89.dtor_name;
          DAST._IType _1715_typ = _source89.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source89.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1716_expression = maybeValue1.dtor_value;
            unmatched89 = false;
            {
              RAST._IType _1717_tpe;
              RAST._IType _out132;
              _out132 = (this).GenType(_1715_typ, DCOMP.GenTypeContext.InBinding());
              _1717_tpe = _out132;
              Dafny.ISequence<Dafny.Rune> _1718_varName;
              _1718_varName = DCOMP.__default.escapeVar(_1714_name);
              bool _1719_hasCopySemantics;
              _1719_hasCopySemantics = (_1717_tpe).CanReadWithoutClone();
              if (((_1716_expression).is_InitializationValue) && (!(_1719_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1718_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.MaybePlaceboPath).AsExpr()).ApplyType1(_1717_tpe)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1718_varName, RAST.__default.MaybePlaceboType(_1717_tpe));
              } else {
                RAST._IExpr _1720_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1721_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1716_expression).is_InitializationValue) && ((_1717_tpe).IsObjectOrPointer())) {
                  _1720_expr = (_1717_tpe).ToNullExpr();
                  _1721_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1722_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out133;
                  DCOMP._IOwnership _out134;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
                  (this).GenExpr(_1716_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
                  _1720_expr = _out133;
                  _1722_exprOwnership = _out134;
                  _1721_recIdents = _out135;
                }
                readIdents = _1721_recIdents;
                _1717_tpe = (((_1716_expression).is_NewUninitArray) ? ((_1717_tpe).TypeAtInitialization()) : (_1717_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1718_varName, Std.Wrappers.Option<RAST._IType>.create_Some(_1717_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1720_expr));
                newEnv = (env).AddAssigned(_1718_varName, _1717_tpe);
              }
            }
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1723_name = _source89.dtor_name;
          DAST._IType _1724_typ = _source89.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source89.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched89 = false;
            {
              DAST._IStatement _1725_newStmt;
              _1725_newStmt = DAST.Statement.create_DeclareVar(_1723_name, _1724_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1724_typ)));
              RAST._IExpr _out136;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
              DCOMP._IEnvironment _out138;
              (this).GenStmt(_1725_newStmt, selfIdent, env, isLast, earlyReturn, out _out136, out _out137, out _out138);
              generated = _out136;
              readIdents = _out137;
              newEnv = _out138;
            }
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Assign) {
          DAST._IAssignLhs _1726_lhs = _source89.dtor_lhs;
          DAST._IExpression _1727_expression = _source89.dtor_value;
          unmatched89 = false;
          {
            RAST._IExpr _1728_exprGen;
            DCOMP._IOwnership _1729___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1730_exprIdents;
            RAST._IExpr _out139;
            DCOMP._IOwnership _out140;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
            (this).GenExpr(_1727_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out139, out _out140, out _out141);
            _1728_exprGen = _out139;
            _1729___v84 = _out140;
            _1730_exprIdents = _out141;
            if ((_1726_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1731_rustId;
              _1731_rustId = DCOMP.__default.escapeVar((_1726_lhs).dtor_ident);
              Std.Wrappers._IOption<RAST._IType> _1732_tpe;
              _1732_tpe = (env).GetType(_1731_rustId);
              if (((_1732_tpe).is_Some) && ((((_1732_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1728_exprGen = RAST.__default.MaybePlacebo(_1728_exprGen);
              }
            }
            if (((_1726_lhs).is_Index) && (((_1726_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1733_rustId;
              _1733_rustId = DCOMP.__default.escapeVar(((_1726_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1734_tpe;
              _1734_tpe = (env).GetType(_1733_rustId);
              if (((_1734_tpe).is_Some) && ((((_1734_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1728_exprGen = RAST.__default.MaybeUninitNew(_1728_exprGen);
              }
            }
            RAST._IExpr _1735_lhsGen;
            bool _1736_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1737_recIdents;
            DCOMP._IEnvironment _1738_resEnv;
            RAST._IExpr _out142;
            bool _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            DCOMP._IEnvironment _out145;
            (this).GenAssignLhs(_1726_lhs, _1728_exprGen, selfIdent, env, out _out142, out _out143, out _out144, out _out145);
            _1735_lhsGen = _out142;
            _1736_needsIIFE = _out143;
            _1737_recIdents = _out144;
            _1738_resEnv = _out145;
            generated = _1735_lhsGen;
            newEnv = _1738_resEnv;
            if (_1736_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1737_recIdents, _1730_exprIdents);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_If) {
          DAST._IExpression _1739_cond = _source89.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1740_thnDafny = _source89.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1741_elsDafny = _source89.dtor_els;
          unmatched89 = false;
          {
            RAST._IExpr _1742_cond;
            DCOMP._IOwnership _1743___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1744_recIdents;
            RAST._IExpr _out146;
            DCOMP._IOwnership _out147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
            (this).GenExpr(_1739_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out146, out _out147, out _out148);
            _1742_cond = _out146;
            _1743___v85 = _out147;
            _1744_recIdents = _out148;
            Dafny.ISequence<Dafny.Rune> _1745_condString;
            _1745_condString = (_1742_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1744_recIdents;
            RAST._IExpr _1746_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1747_thnIdents;
            DCOMP._IEnvironment _1748_thnEnv;
            RAST._IExpr _out149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out150;
            DCOMP._IEnvironment _out151;
            (this).GenStmts(_1740_thnDafny, selfIdent, env, isLast, earlyReturn, out _out149, out _out150, out _out151);
            _1746_thn = _out149;
            _1747_thnIdents = _out150;
            _1748_thnEnv = _out151;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1747_thnIdents);
            RAST._IExpr _1749_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1750_elsIdents;
            DCOMP._IEnvironment _1751_elsEnv;
            RAST._IExpr _out152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
            DCOMP._IEnvironment _out154;
            (this).GenStmts(_1741_elsDafny, selfIdent, env, isLast, earlyReturn, out _out152, out _out153, out _out154);
            _1749_els = _out152;
            _1750_elsIdents = _out153;
            _1751_elsEnv = _out154;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1750_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1742_cond, _1746_thn, _1749_els);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1752_lbl = _source89.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1753_body = _source89.dtor_body;
          unmatched89 = false;
          {
            RAST._IExpr _1754_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1755_bodyIdents;
            DCOMP._IEnvironment _1756_env2;
            RAST._IExpr _out155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
            DCOMP._IEnvironment _out157;
            (this).GenStmts(_1753_body, selfIdent, env, isLast, earlyReturn, out _out155, out _out156, out _out157);
            _1754_body = _out155;
            _1755_bodyIdents = _out156;
            _1756_env2 = _out157;
            readIdents = _1755_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1752_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1754_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_While) {
          DAST._IExpression _1757_cond = _source89.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1758_body = _source89.dtor_body;
          unmatched89 = false;
          {
            RAST._IExpr _1759_cond;
            DCOMP._IOwnership _1760___v86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1761_recIdents;
            RAST._IExpr _out158;
            DCOMP._IOwnership _out159;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
            (this).GenExpr(_1757_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out158, out _out159, out _out160);
            _1759_cond = _out158;
            _1760___v86 = _out159;
            _1761_recIdents = _out160;
            readIdents = _1761_recIdents;
            RAST._IExpr _1762_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1763_bodyIdents;
            DCOMP._IEnvironment _1764_bodyEnv;
            RAST._IExpr _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            DCOMP._IEnvironment _out163;
            (this).GenStmts(_1758_body, selfIdent, env, false, earlyReturn, out _out161, out _out162, out _out163);
            _1762_bodyExpr = _out161;
            _1763_bodyIdents = _out162;
            _1764_bodyEnv = _out163;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1763_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1759_cond), _1762_bodyExpr);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1765_boundName = _source89.dtor_boundName;
          DAST._IType _1766_boundType = _source89.dtor_boundType;
          DAST._IExpression _1767_overExpr = _source89.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1768_body = _source89.dtor_body;
          unmatched89 = false;
          {
            RAST._IExpr _1769_over;
            DCOMP._IOwnership _1770___v87;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1771_recIdents;
            RAST._IExpr _out164;
            DCOMP._IOwnership _out165;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out166;
            (this).GenExpr(_1767_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out164, out _out165, out _out166);
            _1769_over = _out164;
            _1770___v87 = _out165;
            _1771_recIdents = _out166;
            if (((_1767_overExpr).is_MapBoundedPool) || ((_1767_overExpr).is_SetBoundedPool)) {
              _1769_over = ((_1769_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1772_boundTpe;
            RAST._IType _out167;
            _out167 = (this).GenType(_1766_boundType, DCOMP.GenTypeContext.@default());
            _1772_boundTpe = _out167;
            readIdents = _1771_recIdents;
            Dafny.ISequence<Dafny.Rune> _1773_boundRName;
            _1773_boundRName = DCOMP.__default.escapeVar(_1765_boundName);
            RAST._IExpr _1774_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1775_bodyIdents;
            DCOMP._IEnvironment _1776_bodyEnv;
            RAST._IExpr _out168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
            DCOMP._IEnvironment _out170;
            (this).GenStmts(_1768_body, selfIdent, (env).AddAssigned(_1773_boundRName, _1772_boundTpe), false, earlyReturn, out _out168, out _out169, out _out170);
            _1774_bodyExpr = _out168;
            _1775_bodyIdents = _out169;
            _1776_bodyEnv = _out170;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1775_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1773_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1773_boundRName, _1769_over, _1774_bodyExpr);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1777_toLabel = _source89.dtor_toLabel;
          unmatched89 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source90 = _1777_toLabel;
            bool unmatched90 = true;
            if (unmatched90) {
              if (_source90.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1778_lbl = _source90.dtor_value;
                unmatched90 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1778_lbl)));
                }
              }
            }
            if (unmatched90) {
              unmatched90 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1779_body = _source89.dtor_body;
          unmatched89 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1780_selfClone;
              DCOMP._IOwnership _1781___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1782___v89;
              RAST._IExpr _out171;
              DCOMP._IOwnership _out172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out171, out _out172, out _out173);
              _1780_selfClone = _out171;
              _1781___v88 = _out172;
              _1782___v89 = _out173;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1780_selfClone)));
            }
            newEnv = env;
            BigInteger _hi35 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1783_paramI = BigInteger.Zero; _1783_paramI < _hi35; _1783_paramI++) {
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
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1784_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1785_paramInit)));
              if (((env).dtor_types).Contains(_1784_param)) {
                RAST._IType _1788_declaredType;
                _1788_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1784_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1784_param, _1788_declaredType);
              }
            }
            RAST._IExpr _1789_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1790_bodyIdents;
            DCOMP._IEnvironment _1791_bodyEnv;
            RAST._IExpr _out177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out178;
            DCOMP._IEnvironment _out179;
            (this).GenStmts(_1779_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out177, out _out178, out _out179);
            _1789_bodyExpr = _out177;
            _1790_bodyIdents = _out178;
            _1791_bodyEnv = _out179;
            readIdents = _1790_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1789_bodyExpr)));
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_JumpTailCallStart) {
          unmatched89 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Call) {
          DAST._IExpression _1792_on = _source89.dtor_on;
          DAST._ICallName _1793_name = _source89.dtor_callName;
          Dafny.ISequence<DAST._IType> _1794_typeArgs = _source89.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1795_args = _source89.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1796_maybeOutVars = _source89.dtor_outs;
          unmatched89 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1797_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1798_recIdents;
            Dafny.ISequence<RAST._IType> _1799_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1800_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out181;
            Dafny.ISequence<RAST._IType> _out182;
            Std.Wrappers._IOption<DAST._IResolvedType> _out183;
            (this).GenArgs(selfIdent, _1793_name, _1794_typeArgs, _1795_args, env, out _out180, out _out181, out _out182, out _out183);
            _1797_argExprs = _out180;
            _1798_recIdents = _out181;
            _1799_typeExprs = _out182;
            _1800_fullNameQualifier = _out183;
            readIdents = _1798_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source91 = _1800_fullNameQualifier;
            bool unmatched91 = true;
            if (unmatched91) {
              if (_source91.is_Some) {
                DAST._IResolvedType value9 = _source91.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1801_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1802_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1803_base = value9.dtor_kind;
                unmatched91 = false;
                RAST._IExpr _1804_fullPath;
                RAST._IExpr _out184;
                _out184 = DCOMP.COMP.GenPathExpr(_1801_path, true);
                _1804_fullPath = _out184;
                Dafny.ISequence<RAST._IType> _1805_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out185;
                _out185 = (this).GenTypeArgs(_1802_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1805_onTypeExprs = _out185;
                RAST._IExpr _1806_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1807_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1808_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1803_base).is_Trait) || ((_1803_base).is_Class)) {
                  RAST._IExpr _out186;
                  DCOMP._IOwnership _out187;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out188;
                  (this).GenExpr(_1792_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out186, out _out187, out _out188);
                  _1806_onExpr = _out186;
                  _1807_recOwnership = _out187;
                  _1808_recIdents = _out188;
                  _1806_onExpr = ((this).modify__macro).Apply1(_1806_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1808_recIdents);
                } else {
                  RAST._IExpr _out189;
                  DCOMP._IOwnership _out190;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out191;
                  (this).GenExpr(_1792_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out189, out _out190, out _out191);
                  _1806_onExpr = _out189;
                  _1807_recOwnership = _out190;
                  _1808_recIdents = _out191;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1808_recIdents);
                }
                generated = ((((_1804_fullPath).ApplyType(_1805_onTypeExprs)).FSel(DCOMP.__default.escapeName((_1793_name).dtor_name))).ApplyType(_1799_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1806_onExpr), _1797_argExprs));
              }
            }
            if (unmatched91) {
              unmatched91 = false;
              RAST._IExpr _1809_onExpr;
              DCOMP._IOwnership _1810___v96;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1811_enclosingIdents;
              RAST._IExpr _out192;
              DCOMP._IOwnership _out193;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
              (this).GenExpr(_1792_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out192, out _out193, out _out194);
              _1809_onExpr = _out192;
              _1810___v96 = _out193;
              _1811_enclosingIdents = _out194;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1811_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1812_renderedName;
              _1812_renderedName = (this).GetMethodName(_1792_on, _1793_name);
              DAST._IExpression _source92 = _1792_on;
              bool unmatched92 = true;
              if (unmatched92) {
                bool disjunctiveMatch13 = false;
                if (_source92.is_Companion) {
                  disjunctiveMatch13 = true;
                }
                if (_source92.is_ExternCompanion) {
                  disjunctiveMatch13 = true;
                }
                if (disjunctiveMatch13) {
                  unmatched92 = false;
                  {
                    _1809_onExpr = (_1809_onExpr).FSel(_1812_renderedName);
                  }
                }
              }
              if (unmatched92) {
                unmatched92 = false;
                {
                  if (!object.Equals(_1809_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source93 = _1793_name;
                    bool unmatched93 = true;
                    if (unmatched93) {
                      if (_source93.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source93.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1813_tpe = onType0.dtor_value;
                          unmatched93 = false;
                          RAST._IType _1814_typ;
                          RAST._IType _out195;
                          _out195 = (this).GenType(_1813_tpe, DCOMP.GenTypeContext.@default());
                          _1814_typ = _out195;
                          if (((_1814_typ).IsObjectOrPointer()) && (!object.Equals(_1809_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1809_onExpr = ((this).modify__macro).Apply1(_1809_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched93) {
                      unmatched93 = false;
                    }
                  }
                  _1809_onExpr = (_1809_onExpr).Sel(_1812_renderedName);
                }
              }
              generated = ((_1809_onExpr).ApplyType(_1799_typeExprs)).Apply(_1797_argExprs);
            }
            if (((_1796_maybeOutVars).is_Some) && ((new BigInteger(((_1796_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1815_outVar;
              _1815_outVar = DCOMP.__default.escapeVar(((_1796_maybeOutVars).dtor_value).Select(BigInteger.Zero));
              if (!((env).CanReadWithoutClone(_1815_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1815_outVar, generated);
            } else if (((_1796_maybeOutVars).is_None) || ((new BigInteger(((_1796_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1816_tmpVar;
              _1816_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1817_tmpId;
              _1817_tmpId = RAST.Expr.create_Identifier(_1816_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1816_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1818_outVars;
              _1818_outVars = (_1796_maybeOutVars).dtor_value;
              BigInteger _hi36 = new BigInteger((_1818_outVars).Count);
              for (BigInteger _1819_outI = BigInteger.Zero; _1819_outI < _hi36; _1819_outI++) {
                Dafny.ISequence<Dafny.Rune> _1820_outVar;
                _1820_outVar = DCOMP.__default.escapeVar((_1818_outVars).Select(_1819_outI));
                RAST._IExpr _1821_rhs;
                _1821_rhs = (_1817_tmpId).Sel(Std.Strings.__default.OfNat(_1819_outI));
                if (!((env).CanReadWithoutClone(_1820_outVar))) {
                  _1821_rhs = RAST.__default.MaybePlacebo(_1821_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1820_outVar, _1821_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Return) {
          DAST._IExpression _1822_exprDafny = _source89.dtor_expr;
          unmatched89 = false;
          {
            RAST._IExpr _1823_expr;
            DCOMP._IOwnership _1824___v106;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1825_recIdents;
            RAST._IExpr _out196;
            DCOMP._IOwnership _out197;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out198;
            (this).GenExpr(_1822_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out196, out _out197, out _out198);
            _1823_expr = _out196;
            _1824___v106 = _out197;
            _1825_recIdents = _out198;
            readIdents = _1825_recIdents;
            if (isLast) {
              generated = _1823_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1823_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_EarlyReturn) {
          unmatched89 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source94 = earlyReturn;
            bool unmatched94 = true;
            if (unmatched94) {
              if (_source94.is_None) {
                unmatched94 = false;
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
              }
            }
            if (unmatched94) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1826_rustIdents = _source94.dtor_value;
              unmatched94 = false;
              Dafny.ISequence<RAST._IExpr> _1827_tupleArgs;
              _1827_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi37 = new BigInteger((_1826_rustIdents).Count);
              for (BigInteger _1828_i = BigInteger.Zero; _1828_i < _hi37; _1828_i++) {
                RAST._IExpr _1829_rIdent;
                DCOMP._IOwnership _1830___v107;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1831___v108;
                RAST._IExpr _out199;
                DCOMP._IOwnership _out200;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
                (this).GenIdent((_1826_rustIdents).Select(_1828_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out199, out _out200, out _out201);
                _1829_rIdent = _out199;
                _1830___v107 = _out200;
                _1831___v108 = _out201;
                _1827_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1827_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1829_rIdent));
              }
              if ((new BigInteger((_1827_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1827_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1827_tupleArgs)));
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Halt) {
          unmatched89 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched89) {
        DAST._IExpression _1832_e = _source89.dtor_Print_a0;
        unmatched89 = false;
        {
          RAST._IExpr _1833_printedExpr;
          DCOMP._IOwnership _1834_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1835_recIdents;
          RAST._IExpr _out202;
          DCOMP._IOwnership _out203;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out204;
          (this).GenExpr(_1832_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out202, out _out203, out _out204);
          _1833_printedExpr = _out202;
          _1834_recOwnership = _out203;
          _1835_recIdents = _out204;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).AsExpr()).Apply1(_1833_printedExpr)));
          readIdents = _1835_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeRangeToRustType(DAST._INewtypeRange range) {
      DAST._INewtypeRange _source95 = range;
      bool unmatched95 = true;
      if (unmatched95) {
        if (_source95.is_NoRange) {
          unmatched95 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched95) {
        if (_source95.is_U8) {
          unmatched95 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched95) {
        if (_source95.is_U16) {
          unmatched95 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched95) {
        if (_source95.is_U32) {
          unmatched95 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched95) {
        if (_source95.is_U64) {
          unmatched95 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched95) {
        if (_source95.is_U128) {
          unmatched95 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched95) {
        if (_source95.is_I8) {
          unmatched95 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched95) {
        if (_source95.is_I16) {
          unmatched95 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched95) {
        if (_source95.is_I32) {
          unmatched95 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched95) {
        if (_source95.is_I64) {
          unmatched95 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched95) {
        if (_source95.is_I128) {
          unmatched95 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched95) {
        unmatched95 = false;
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
      DAST._IExpression _source96 = e;
      bool unmatched96 = true;
      if (unmatched96) {
        if (_source96.is_Literal) {
          DAST._ILiteral _h170 = _source96.dtor_Literal_a0;
          if (_h170.is_BoolLiteral) {
            bool _1836_b = _h170.dtor_BoolLiteral_a0;
            unmatched96 = false;
            {
              RAST._IExpr _out209;
              DCOMP._IOwnership _out210;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1836_b), expectedOwnership, out _out209, out _out210);
              r = _out209;
              resultingOwnership = _out210;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched96) {
        if (_source96.is_Literal) {
          DAST._ILiteral _h171 = _source96.dtor_Literal_a0;
          if (_h171.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1837_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1838_t = _h171.dtor_IntLiteral_a1;
            unmatched96 = false;
            {
              DAST._IType _source97 = _1838_t;
              bool unmatched97 = true;
              if (unmatched97) {
                if (_source97.is_Primitive) {
                  DAST._IPrimitive _h70 = _source97.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched97 = false;
                    {
                      if ((new BigInteger((_1837_i).Count)) <= (new BigInteger(4))) {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralInt(_1837_i));
                      } else {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1837_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched97) {
                DAST._IType _1839_o = _source97;
                unmatched97 = false;
                {
                  RAST._IType _1840_genType;
                  RAST._IType _out211;
                  _out211 = (this).GenType(_1839_o, DCOMP.GenTypeContext.@default());
                  _1840_genType = _out211;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1837_i), _1840_genType);
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
      if (unmatched96) {
        if (_source96.is_Literal) {
          DAST._ILiteral _h172 = _source96.dtor_Literal_a0;
          if (_h172.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1841_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1842_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1843_t = _h172.dtor_DecLiteral_a2;
            unmatched96 = false;
            {
              DAST._IType _source98 = _1843_t;
              bool unmatched98 = true;
              if (unmatched98) {
                if (_source98.is_Primitive) {
                  DAST._IPrimitive _h71 = _source98.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched98 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1841_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1842_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched98) {
                DAST._IType _1844_o = _source98;
                unmatched98 = false;
                {
                  RAST._IType _1845_genType;
                  RAST._IType _out214;
                  _out214 = (this).GenType(_1844_o, DCOMP.GenTypeContext.@default());
                  _1845_genType = _out214;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1841_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1842_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1845_genType);
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
      if (unmatched96) {
        if (_source96.is_Literal) {
          DAST._ILiteral _h173 = _source96.dtor_Literal_a0;
          if (_h173.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1846_l = _h173.dtor_StringLiteral_a0;
            bool _1847_verbatim = _h173.dtor_verbatim;
            unmatched96 = false;
            {
              r = (((RAST.__default.dafny__runtime).MSel((this).string__of)).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1846_l, false, _1847_verbatim));
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
      if (unmatched96) {
        if (_source96.is_Literal) {
          DAST._ILiteral _h174 = _source96.dtor_Literal_a0;
          if (_h174.is_CharLiteralUTF16) {
            BigInteger _1848_c = _h174.dtor_CharLiteralUTF16_a0;
            unmatched96 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1848_c));
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
      if (unmatched96) {
        if (_source96.is_Literal) {
          DAST._ILiteral _h175 = _source96.dtor_Literal_a0;
          if (_h175.is_CharLiteral) {
            Dafny.Rune _1849_c = _h175.dtor_CharLiteral_a0;
            unmatched96 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1849_c).Value)));
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
      if (unmatched96) {
        DAST._ILiteral _h176 = _source96.dtor_Literal_a0;
        DAST._IType _1850_tpe = _h176.dtor_Null_a0;
        unmatched96 = false;
        {
          RAST._IType _1851_tpeGen;
          RAST._IType _out223;
          _out223 = (this).GenType(_1850_tpe, DCOMP.GenTypeContext.@default());
          _1851_tpeGen = _out223;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null_mut"));
          } else {
            r = RAST.Expr.create_TypeAscription((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1851_tpeGen);
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
      DAST._IBinOp _1852_op = _let_tmp_rhs56.dtor_op;
      DAST._IExpression _1853_lExpr = _let_tmp_rhs56.dtor_left;
      DAST._IExpression _1854_rExpr = _let_tmp_rhs56.dtor_right;
      DAST.Format._IBinaryOpFormat _1855_format = _let_tmp_rhs56.dtor_format2;
      bool _1856_becomesLeftCallsRight;
      _1856_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source99 = _1852_op;
        bool unmatched99 = true;
        if (unmatched99) {
          bool disjunctiveMatch14 = false;
          if (_source99.is_SetMerge) {
            disjunctiveMatch14 = true;
          }
          if (_source99.is_SetSubtraction) {
            disjunctiveMatch14 = true;
          }
          if (_source99.is_SetIntersection) {
            disjunctiveMatch14 = true;
          }
          if (_source99.is_SetDisjoint) {
            disjunctiveMatch14 = true;
          }
          if (_source99.is_MapMerge) {
            disjunctiveMatch14 = true;
          }
          if (_source99.is_MapSubtraction) {
            disjunctiveMatch14 = true;
          }
          if (_source99.is_MultisetMerge) {
            disjunctiveMatch14 = true;
          }
          if (_source99.is_MultisetSubtraction) {
            disjunctiveMatch14 = true;
          }
          if (_source99.is_MultisetIntersection) {
            disjunctiveMatch14 = true;
          }
          if (_source99.is_MultisetDisjoint) {
            disjunctiveMatch14 = true;
          }
          if (_source99.is_Concat) {
            disjunctiveMatch14 = true;
          }
          if (disjunctiveMatch14) {
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
      bool _1857_becomesRightCallsLeft;
      _1857_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source100 = _1852_op;
        bool unmatched100 = true;
        if (unmatched100) {
          if (_source100.is_In) {
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
      bool _1858_becomesCallLeftRight;
      _1858_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source101 = _1852_op;
        bool unmatched101 = true;
        if (unmatched101) {
          if (_source101.is_Eq) {
            bool referential0 = _source101.dtor_referential;
            if ((referential0) == (true)) {
              unmatched101 = false;
              return false;
            }
          }
        }
        if (unmatched101) {
          if (_source101.is_SetMerge) {
            unmatched101 = false;
            return true;
          }
        }
        if (unmatched101) {
          if (_source101.is_SetSubtraction) {
            unmatched101 = false;
            return true;
          }
        }
        if (unmatched101) {
          if (_source101.is_SetIntersection) {
            unmatched101 = false;
            return true;
          }
        }
        if (unmatched101) {
          if (_source101.is_SetDisjoint) {
            unmatched101 = false;
            return true;
          }
        }
        if (unmatched101) {
          if (_source101.is_MapMerge) {
            unmatched101 = false;
            return true;
          }
        }
        if (unmatched101) {
          if (_source101.is_MapSubtraction) {
            unmatched101 = false;
            return true;
          }
        }
        if (unmatched101) {
          if (_source101.is_MultisetMerge) {
            unmatched101 = false;
            return true;
          }
        }
        if (unmatched101) {
          if (_source101.is_MultisetSubtraction) {
            unmatched101 = false;
            return true;
          }
        }
        if (unmatched101) {
          if (_source101.is_MultisetIntersection) {
            unmatched101 = false;
            return true;
          }
        }
        if (unmatched101) {
          if (_source101.is_MultisetDisjoint) {
            unmatched101 = false;
            return true;
          }
        }
        if (unmatched101) {
          if (_source101.is_Concat) {
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
      DCOMP._IOwnership _1859_expectedLeftOwnership;
      _1859_expectedLeftOwnership = ((_1856_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1857_becomesRightCallsLeft) || (_1858_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1860_expectedRightOwnership;
      _1860_expectedRightOwnership = (((_1856_becomesLeftCallsRight) || (_1858_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1857_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1861_left;
      DCOMP._IOwnership _1862___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1863_recIdentsL;
      RAST._IExpr _out226;
      DCOMP._IOwnership _out227;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
      (this).GenExpr(_1853_lExpr, selfIdent, env, _1859_expectedLeftOwnership, out _out226, out _out227, out _out228);
      _1861_left = _out226;
      _1862___v113 = _out227;
      _1863_recIdentsL = _out228;
      RAST._IExpr _1864_right;
      DCOMP._IOwnership _1865___v114;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1866_recIdentsR;
      RAST._IExpr _out229;
      DCOMP._IOwnership _out230;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out231;
      (this).GenExpr(_1854_rExpr, selfIdent, env, _1860_expectedRightOwnership, out _out229, out _out230, out _out231);
      _1864_right = _out229;
      _1865___v114 = _out230;
      _1866_recIdentsR = _out231;
      DAST._IBinOp _source102 = _1852_op;
      bool unmatched102 = true;
      if (unmatched102) {
        if (_source102.is_In) {
          unmatched102 = false;
          {
            r = ((_1864_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1861_left);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_SeqProperPrefix) {
          unmatched102 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1861_left, _1864_right, _1855_format);
        }
      }
      if (unmatched102) {
        if (_source102.is_SeqPrefix) {
          unmatched102 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1861_left, _1864_right, _1855_format);
        }
      }
      if (unmatched102) {
        if (_source102.is_SetMerge) {
          unmatched102 = false;
          {
            r = ((_1861_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1864_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_SetSubtraction) {
          unmatched102 = false;
          {
            r = ((_1861_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1864_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_SetIntersection) {
          unmatched102 = false;
          {
            r = ((_1861_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1864_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_Subset) {
          unmatched102 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1861_left, _1864_right, _1855_format);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_ProperSubset) {
          unmatched102 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1861_left, _1864_right, _1855_format);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_SetDisjoint) {
          unmatched102 = false;
          {
            r = ((_1861_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1864_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_MapMerge) {
          unmatched102 = false;
          {
            r = ((_1861_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1864_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_MapSubtraction) {
          unmatched102 = false;
          {
            r = ((_1861_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1864_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_MultisetMerge) {
          unmatched102 = false;
          {
            r = ((_1861_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1864_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_MultisetSubtraction) {
          unmatched102 = false;
          {
            r = ((_1861_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1864_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_MultisetIntersection) {
          unmatched102 = false;
          {
            r = ((_1861_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1864_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_Submultiset) {
          unmatched102 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1861_left, _1864_right, _1855_format);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_ProperSubmultiset) {
          unmatched102 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1861_left, _1864_right, _1855_format);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_MultisetDisjoint) {
          unmatched102 = false;
          {
            r = ((_1861_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1864_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_Concat) {
          unmatched102 = false;
          {
            r = ((_1861_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1864_right);
          }
        }
      }
      if (unmatched102) {
        unmatched102 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1852_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1852_op), _1861_left, _1864_right, _1855_format);
          } else {
            DAST._IBinOp _source103 = _1852_op;
            bool unmatched103 = true;
            if (unmatched103) {
              if (_source103.is_Eq) {
                bool _1867_referential = _source103.dtor_referential;
                unmatched103 = false;
                {
                  if (_1867_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1861_left, _1864_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1854_rExpr).is_SeqValue) && ((new BigInteger(((_1854_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1861_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1853_lExpr).is_SeqValue) && ((new BigInteger(((_1853_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1864_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1861_left, _1864_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched103) {
              if (_source103.is_EuclidianDiv) {
                unmatched103 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1861_left, _1864_right));
                }
              }
            }
            if (unmatched103) {
              if (_source103.is_EuclidianMod) {
                unmatched103 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1861_left, _1864_right));
                }
              }
            }
            if (unmatched103) {
              Dafny.ISequence<Dafny.Rune> _1868_op = _source103.dtor_Passthrough_a0;
              unmatched103 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1868_op, _1861_left, _1864_right, _1855_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1863_recIdentsL, _1866_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs57 = e;
      DAST._IExpression _1869_expr = _let_tmp_rhs57.dtor_value;
      DAST._IType _1870_fromTpe = _let_tmp_rhs57.dtor_from;
      DAST._IType _1871_toTpe = _let_tmp_rhs57.dtor_typ;
      DAST._IType _let_tmp_rhs58 = _1871_toTpe;
      DAST._IResolvedType _let_tmp_rhs59 = _let_tmp_rhs58.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1872_path = _let_tmp_rhs59.dtor_path;
      Dafny.ISequence<DAST._IType> _1873_typeArgs = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs60 = _let_tmp_rhs59.dtor_kind;
      DAST._IType _1874_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _1875_range = _let_tmp_rhs60.dtor_range;
      bool _1876_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1877___v116 = _let_tmp_rhs59.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1878___v117 = _let_tmp_rhs59.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1879___v118 = _let_tmp_rhs59.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1880_nativeToType;
      _1880_nativeToType = DCOMP.COMP.NewtypeRangeToRustType(_1875_range);
      if (object.Equals(_1870_fromTpe, _1874_b)) {
        RAST._IExpr _1881_recursiveGen;
        DCOMP._IOwnership _1882_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1883_recIdents;
        RAST._IExpr _out234;
        DCOMP._IOwnership _out235;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out236;
        (this).GenExpr(_1869_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out234, out _out235, out _out236);
        _1881_recursiveGen = _out234;
        _1882_recOwned = _out235;
        _1883_recIdents = _out236;
        readIdents = _1883_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source104 = _1880_nativeToType;
        bool unmatched104 = true;
        if (unmatched104) {
          if (_source104.is_Some) {
            RAST._IType _1884_v = _source104.dtor_value;
            unmatched104 = false;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1881_recursiveGen, RAST.Expr.create_ExprFromType(_1884_v)));
            RAST._IExpr _out237;
            DCOMP._IOwnership _out238;
            (this).FromOwned(r, expectedOwnership, out _out237, out _out238);
            r = _out237;
            resultingOwnership = _out238;
          }
        }
        if (unmatched104) {
          unmatched104 = false;
          if (_1876_erase) {
            r = _1881_recursiveGen;
          } else {
            RAST._IType _1885_rhsType;
            RAST._IType _out239;
            _out239 = (this).GenType(_1871_toTpe, DCOMP.GenTypeContext.InBinding());
            _1885_rhsType = _out239;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1885_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1881_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out240;
          DCOMP._IOwnership _out241;
          (this).FromOwnership(r, _1882_recOwned, expectedOwnership, out _out240, out _out241);
          r = _out240;
          resultingOwnership = _out241;
        }
      } else {
        if ((_1880_nativeToType).is_Some) {
          DAST._IType _source105 = _1870_fromTpe;
          bool unmatched105 = true;
          if (unmatched105) {
            if (_source105.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source105.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1886_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1887_range0 = kind1.dtor_range;
                bool _1888_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1889_attributes0 = resolved1.dtor_attributes;
                unmatched105 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1890_nativeFromType;
                  _1890_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1887_range0);
                  if ((_1890_nativeFromType).is_Some) {
                    RAST._IExpr _1891_recursiveGen;
                    DCOMP._IOwnership _1892_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1893_recIdents;
                    RAST._IExpr _out242;
                    DCOMP._IOwnership _out243;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out244;
                    (this).GenExpr(_1869_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out242, out _out243, out _out244);
                    _1891_recursiveGen = _out242;
                    _1892_recOwned = _out243;
                    _1893_recIdents = _out244;
                    RAST._IExpr _out245;
                    DCOMP._IOwnership _out246;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1891_recursiveGen, (_1880_nativeToType).dtor_value), _1892_recOwned, expectedOwnership, out _out245, out _out246);
                    r = _out245;
                    resultingOwnership = _out246;
                    readIdents = _1893_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched105) {
            unmatched105 = false;
          }
          if (object.Equals(_1870_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1894_recursiveGen;
            DCOMP._IOwnership _1895_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1896_recIdents;
            RAST._IExpr _out247;
            DCOMP._IOwnership _out248;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
            (this).GenExpr(_1869_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out247, out _out248, out _out249);
            _1894_recursiveGen = _out247;
            _1895_recOwned = _out248;
            _1896_recIdents = _out249;
            RAST._IExpr _out250;
            DCOMP._IOwnership _out251;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1894_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1880_nativeToType).dtor_value), _1895_recOwned, expectedOwnership, out _out250, out _out251);
            r = _out250;
            resultingOwnership = _out251;
            readIdents = _1896_recIdents;
            return ;
          }
        }
        RAST._IExpr _out252;
        DCOMP._IOwnership _out253;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out254;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1869_expr, _1870_fromTpe, _1874_b), _1874_b, _1871_toTpe), selfIdent, env, expectedOwnership, out _out252, out _out253, out _out254);
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
      DAST._IExpression _1897_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _1898_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _1899_toTpe = _let_tmp_rhs61.dtor_typ;
      DAST._IType _let_tmp_rhs62 = _1898_fromTpe;
      DAST._IResolvedType _let_tmp_rhs63 = _let_tmp_rhs62.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1900___v124 = _let_tmp_rhs63.dtor_path;
      Dafny.ISequence<DAST._IType> _1901___v125 = _let_tmp_rhs63.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs64 = _let_tmp_rhs63.dtor_kind;
      DAST._IType _1902_b = _let_tmp_rhs64.dtor_baseType;
      DAST._INewtypeRange _1903_range = _let_tmp_rhs64.dtor_range;
      bool _1904_erase = _let_tmp_rhs64.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1905_attributes = _let_tmp_rhs63.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1906___v126 = _let_tmp_rhs63.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1907___v127 = _let_tmp_rhs63.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1908_nativeFromType;
      _1908_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1903_range);
      if (object.Equals(_1902_b, _1899_toTpe)) {
        RAST._IExpr _1909_recursiveGen;
        DCOMP._IOwnership _1910_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1911_recIdents;
        RAST._IExpr _out255;
        DCOMP._IOwnership _out256;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out257;
        (this).GenExpr(_1897_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out255, out _out256, out _out257);
        _1909_recursiveGen = _out255;
        _1910_recOwned = _out256;
        _1911_recIdents = _out257;
        readIdents = _1911_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source106 = _1908_nativeFromType;
        bool unmatched106 = true;
        if (unmatched106) {
          if (_source106.is_Some) {
            RAST._IType _1912_v = _source106.dtor_value;
            unmatched106 = false;
            RAST._IType _1913_toTpeRust;
            RAST._IType _out258;
            _out258 = (this).GenType(_1899_toTpe, DCOMP.GenTypeContext.@default());
            _1913_toTpeRust = _out258;
            r = ((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1913_toTpeRust))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1909_recursiveGen));
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            (this).FromOwned(r, expectedOwnership, out _out259, out _out260);
            r = _out259;
            resultingOwnership = _out260;
          }
        }
        if (unmatched106) {
          unmatched106 = false;
          if (_1904_erase) {
            r = _1909_recursiveGen;
          } else {
            r = (_1909_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out261;
          DCOMP._IOwnership _out262;
          (this).FromOwnership(r, _1910_recOwned, expectedOwnership, out _out261, out _out262);
          r = _out261;
          resultingOwnership = _out262;
        }
      } else {
        if ((_1908_nativeFromType).is_Some) {
          if (object.Equals(_1899_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1914_recursiveGen;
            DCOMP._IOwnership _1915_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1916_recIdents;
            RAST._IExpr _out263;
            DCOMP._IOwnership _out264;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out265;
            (this).GenExpr(_1897_expr, selfIdent, env, expectedOwnership, out _out263, out _out264, out _out265);
            _1914_recursiveGen = _out263;
            _1915_recOwned = _out264;
            _1916_recIdents = _out265;
            RAST._IExpr _out266;
            DCOMP._IOwnership _out267;
            (this).FromOwnership((((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(RAST.Expr.create_TypeAscription(_1914_recursiveGen, (this).DafnyCharUnderlying)), _1915_recOwned, expectedOwnership, out _out266, out _out267);
            r = _out266;
            resultingOwnership = _out267;
            readIdents = _1916_recIdents;
            return ;
          }
        }
        RAST._IExpr _out268;
        DCOMP._IOwnership _out269;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1897_expr, _1898_fromTpe, _1902_b), _1902_b, _1899_toTpe), selfIdent, env, expectedOwnership, out _out268, out _out269, out _out270);
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
        Std.Wrappers._IResult<__T, __E> _1917_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1917_valueOrError0).IsFailure()) {
          return (_1917_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1918_head = (_1917_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1919_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1919_valueOrError1).IsFailure()) {
            return (_1919_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1920_tail = (_1919_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1918_head), _1920_tail));
          }
        }
      }
    }
    public Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> UpcastConversionLambda(DAST._IType fromType, RAST._IType fromTpe, DAST._IType toType, RAST._IType toTpe, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> typeParams)
    {
      var _pat_let_tv194 = fromType;
      var _pat_let_tv195 = fromTpe;
      var _pat_let_tv196 = toType;
      var _pat_let_tv197 = toTpe;
      var _pat_let_tv198 = typeParams;
      if (object.Equals(fromTpe, toTpe)) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_id"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(fromTpe))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
      } else if (((fromTpe).IsObjectOrPointer()) && ((toTpe).IsObjectOrPointer())) {
        if (!(((toTpe).ObjectOrPointerUnderlying()).is_DynType)) {
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Failure(_System.Tuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>.create(fromType, fromTpe, toType, toTpe, typeParams));
        } else {
          RAST._IType _1921_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1922_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel((this).upcast)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1921_fromTpeUnderlying, _1922_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1923_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1923_valueOrError0).IsFailure()) {
          return (_1923_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1924_lambda = (_1923_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1924_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).AsExpr()).Apply1(_1924_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Dafny.ISequence<BigInteger> _1925_indices = ((((fromType).is_UserDefined) && ((((fromType).dtor_resolved).dtor_kind).is_Datatype)) ? (Std.Collections.Seq.__default.Filter<BigInteger>(Dafny.Helpers.Id<Func<RAST._IType, DAST._IType, Func<BigInteger, bool>>>((_1926_fromTpe, _1927_fromType) => ((System.Func<BigInteger, bool>)((_1928_i) => {
          return ((((_1928_i).Sign != -1) && ((_1928_i) < (new BigInteger(((_1926_fromTpe).dtor_arguments).Count)))) ? (!(((_1928_i).Sign != -1) && ((_1928_i) < (new BigInteger(((((_1927_fromType).dtor_resolved).dtor_kind).dtor_variances).Count)))) || (!((((((_1927_fromType).dtor_resolved).dtor_kind).dtor_variances).Select(_1928_i)).is_Nonvariant))) : (false));
        })))(fromTpe, fromType), ((System.Func<Dafny.ISequence<BigInteger>>) (() => {
          BigInteger dim14 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr14 = new BigInteger[Dafny.Helpers.ToIntChecked(dim14, "array size exceeds memory limit")];
          for (int i14 = 0; i14 < dim14; i14++) {
            var _1929_i = (BigInteger) i14;
            arr14[(int)(_1929_i)] = _1929_i;
          }
          return Dafny.Sequence<BigInteger>.FromArray(arr14);
        }))())) : (((System.Func<Dafny.ISequence<BigInteger>>) (() => {
          BigInteger dim15 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr15 = new BigInteger[Dafny.Helpers.ToIntChecked(dim15, "array size exceeds memory limit")];
          for (int i15 = 0; i15 < dim15; i15++) {
            var _1930_i = (BigInteger) i15;
            arr15[(int)(_1930_i)] = _1930_i;
          }
          return Dafny.Sequence<BigInteger>.FromArray(arr15);
        }))()));
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1931_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim16 = new BigInteger((_1925_indices).Count);
          var arr16 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim16, "array size exceeds memory limit")];
          for (int i16 = 0; i16 < dim16; i16++) {
            var _1932_j = (BigInteger) i16;
            arr16[(int)(_1932_j)] = Dafny.Helpers.Let<BigInteger, Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>((_1925_indices).Select(_1932_j), _pat_let49_0 => Dafny.Helpers.Let<BigInteger, Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>(_pat_let49_0, _1933_i => (this).UpcastConversionLambda((((_pat_let_tv194).dtor_resolved).dtor_typeArgs).Select(_1933_i), ((_pat_let_tv195).dtor_arguments).Select(_1933_i), (((_pat_let_tv196).dtor_resolved).dtor_typeArgs).Select(_1933_i), ((_pat_let_tv197).dtor_arguments).Select(_1933_i), _pat_let_tv198)));
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr16);
        }))());
        if ((_1931_valueOrError1).IsFailure()) {
          return (_1931_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1934_lambdas = (_1931_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim17 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr17 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim17, "array size exceeds memory limit")];
  for (int i17 = 0; i17 < dim17; i17++) {
    var _1935_i = (BigInteger) i17;
    arr17[(int)(_1935_i)] = ((fromTpe).dtor_arguments).Select(_1935_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr17);
}))())).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1934_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1936_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1937_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1938_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1939_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1940_valueOrError2 = (this).UpcastConversionLambda(_1938_newFromType, _1936_newFromTpe, _1939_newToType, _1937_newToTpe, typeParams);
        if ((_1940_valueOrError2).IsFailure()) {
          return (_1940_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1941_coerceArg = (_1940_valueOrError2).Extract();
          RAST._IPath _1942_collectionType = (RAST.__default.dafny__runtime).MSel(((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name);
          RAST._IExpr _1943_baseType = (((((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? (((_1942_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((((fromTpe).Expand()).dtor_arguments).Select(BigInteger.Zero), _1936_newFromTpe))) : (((_1942_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1936_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1943_baseType).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1941_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1944_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1944_valueOrError3).IsFailure()) {
          return (_1944_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1945_lambda = (_1944_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1945_lambda));
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
      DAST._IExpression _1946_expr = _let_tmp_rhs65.dtor_value;
      DAST._IType _1947_fromTpe = _let_tmp_rhs65.dtor_from;
      DAST._IType _1948_toTpe = _let_tmp_rhs65.dtor_typ;
      RAST._IType _1949_fromTpeGen;
      RAST._IType _out271;
      _out271 = (this).GenType(_1947_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1949_fromTpeGen = _out271;
      RAST._IType _1950_toTpeGen;
      RAST._IType _out272;
      _out272 = (this).GenType(_1948_toTpe, DCOMP.GenTypeContext.InBinding());
      _1950_toTpeGen = _out272;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1951_upcastConverter;
      _1951_upcastConverter = (this).UpcastConversionLambda(_1947_fromTpe, _1949_fromTpeGen, _1948_toTpe, _1950_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1951_upcastConverter).is_Success) {
        RAST._IExpr _1952_conversionLambda;
        _1952_conversionLambda = (_1951_upcastConverter).dtor_value;
        RAST._IExpr _1953_recursiveGen;
        DCOMP._IOwnership _1954_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1955_recIdents;
        RAST._IExpr _out273;
        DCOMP._IOwnership _out274;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out275;
        (this).GenExpr(_1946_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out273, out _out274, out _out275);
        _1953_recursiveGen = _out273;
        _1954_recOwned = _out274;
        _1955_recIdents = _out275;
        readIdents = _1955_recIdents;
        r = (_1952_conversionLambda).Apply1(_1953_recursiveGen);
        RAST._IExpr _out276;
        DCOMP._IOwnership _out277;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out276, out _out277);
        r = _out276;
        resultingOwnership = _out277;
      } else if ((this).IsDowncastConversion(_1949_fromTpeGen, _1950_toTpeGen)) {
        RAST._IExpr _1956_recursiveGen;
        DCOMP._IOwnership _1957_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1958_recIdents;
        RAST._IExpr _out278;
        DCOMP._IOwnership _out279;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out280;
        (this).GenExpr(_1946_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out278, out _out279, out _out280);
        _1956_recursiveGen = _out278;
        _1957_recOwned = _out279;
        _1958_recIdents = _out280;
        readIdents = _1958_recIdents;
        _1950_toTpeGen = (_1950_toTpeGen).ObjectOrPointerUnderlying();
        r = (((RAST.__default.dafny__runtime).MSel((this).downcast)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1956_recursiveGen, RAST.Expr.create_ExprFromType(_1950_toTpeGen)));
        RAST._IExpr _out281;
        DCOMP._IOwnership _out282;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out281, out _out282);
        r = _out281;
        resultingOwnership = _out282;
      } else {
        RAST._IExpr _1959_recursiveGen;
        DCOMP._IOwnership _1960_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1961_recIdents;
        RAST._IExpr _out283;
        DCOMP._IOwnership _out284;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out285;
        (this).GenExpr(_1946_expr, selfIdent, env, expectedOwnership, out _out283, out _out284, out _out285);
        _1959_recursiveGen = _out283;
        _1960_recOwned = _out284;
        _1961_recIdents = _out285;
        readIdents = _1961_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs66 = _1951_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs67 = _let_tmp_rhs66.dtor_error;
        DAST._IType _1962_fromType = _let_tmp_rhs67.dtor__0;
        RAST._IType _1963_fromTpeGen = _let_tmp_rhs67.dtor__1;
        DAST._IType _1964_toType = _let_tmp_rhs67.dtor__2;
        RAST._IType _1965_toTpeGen = _let_tmp_rhs67.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1966_m = _let_tmp_rhs67.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1967_msg;
        _1967_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1963_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1965_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1967_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1959_recursiveGen)._ToString(DCOMP.__default.IND), _1967_msg));
        RAST._IExpr _out286;
        DCOMP._IOwnership _out287;
        (this).FromOwnership(r, _1960_recOwned, expectedOwnership, out _out286, out _out287);
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
      DAST._IExpression _1968_expr = _let_tmp_rhs68.dtor_value;
      DAST._IType _1969_fromTpe = _let_tmp_rhs68.dtor_from;
      DAST._IType _1970_toTpe = _let_tmp_rhs68.dtor_typ;
      if (object.Equals(_1969_fromTpe, _1970_toTpe)) {
        RAST._IExpr _1971_recursiveGen;
        DCOMP._IOwnership _1972_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1973_recIdents;
        RAST._IExpr _out288;
        DCOMP._IOwnership _out289;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
        (this).GenExpr(_1968_expr, selfIdent, env, expectedOwnership, out _out288, out _out289, out _out290);
        _1971_recursiveGen = _out288;
        _1972_recOwned = _out289;
        _1973_recIdents = _out290;
        r = _1971_recursiveGen;
        RAST._IExpr _out291;
        DCOMP._IOwnership _out292;
        (this).FromOwnership(r, _1972_recOwned, expectedOwnership, out _out291, out _out292);
        r = _out291;
        resultingOwnership = _out292;
        readIdents = _1973_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source107 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1969_fromTpe, _1970_toTpe);
        bool unmatched107 = true;
        if (unmatched107) {
          DAST._IType _10 = _source107.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1974_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1975_range = kind2.dtor_range;
              bool _1976_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1977_attributes = resolved2.dtor_attributes;
              unmatched107 = false;
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
        if (unmatched107) {
          DAST._IType _00 = _source107.dtor__0;
          if (_00.is_UserDefined) {
            DAST._IResolvedType resolved3 = _00.dtor_resolved;
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1978_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1979_range = kind3.dtor_range;
              bool _1980_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1981_attributes = resolved3.dtor_attributes;
              unmatched107 = false;
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
        if (unmatched107) {
          DAST._IType _01 = _source107.dtor__0;
          if (_01.is_Primitive) {
            DAST._IPrimitive _h72 = _01.dtor_Primitive_a0;
            if (_h72.is_Int) {
              DAST._IType _11 = _source107.dtor__1;
              if (_11.is_Primitive) {
                DAST._IPrimitive _h73 = _11.dtor_Primitive_a0;
                if (_h73.is_Real) {
                  unmatched107 = false;
                  {
                    RAST._IExpr _1982_recursiveGen;
                    DCOMP._IOwnership _1983___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1984_recIdents;
                    RAST._IExpr _out299;
                    DCOMP._IOwnership _out300;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out301;
                    (this).GenExpr(_1968_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out299, out _out300, out _out301);
                    _1982_recursiveGen = _out299;
                    _1983___v138 = _out300;
                    _1984_recIdents = _out301;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1982_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out302;
                    DCOMP._IOwnership _out303;
                    (this).FromOwned(r, expectedOwnership, out _out302, out _out303);
                    r = _out302;
                    resultingOwnership = _out303;
                    readIdents = _1984_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched107) {
          DAST._IType _02 = _source107.dtor__0;
          if (_02.is_Primitive) {
            DAST._IPrimitive _h74 = _02.dtor_Primitive_a0;
            if (_h74.is_Real) {
              DAST._IType _12 = _source107.dtor__1;
              if (_12.is_Primitive) {
                DAST._IPrimitive _h75 = _12.dtor_Primitive_a0;
                if (_h75.is_Int) {
                  unmatched107 = false;
                  {
                    RAST._IExpr _1985_recursiveGen;
                    DCOMP._IOwnership _1986___v139;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1987_recIdents;
                    RAST._IExpr _out304;
                    DCOMP._IOwnership _out305;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out306;
                    (this).GenExpr(_1968_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out304, out _out305, out _out306);
                    _1985_recursiveGen = _out304;
                    _1986___v139 = _out305;
                    _1987_recIdents = _out306;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1985_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out307;
                    DCOMP._IOwnership _out308;
                    (this).FromOwned(r, expectedOwnership, out _out307, out _out308);
                    r = _out307;
                    resultingOwnership = _out308;
                    readIdents = _1987_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched107) {
          DAST._IType _03 = _source107.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h76 = _03.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _13 = _source107.dtor__1;
              if (_13.is_Passthrough) {
                unmatched107 = false;
                {
                  RAST._IType _1988_rhsType;
                  RAST._IType _out309;
                  _out309 = (this).GenType(_1970_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1988_rhsType = _out309;
                  RAST._IExpr _1989_recursiveGen;
                  DCOMP._IOwnership _1990___v141;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1991_recIdents;
                  RAST._IExpr _out310;
                  DCOMP._IOwnership _out311;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out312;
                  (this).GenExpr(_1968_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out310, out _out311, out _out312);
                  _1989_recursiveGen = _out310;
                  _1990___v141 = _out311;
                  _1991_recIdents = _out312;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1988_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1989_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out313;
                  DCOMP._IOwnership _out314;
                  (this).FromOwned(r, expectedOwnership, out _out313, out _out314);
                  r = _out313;
                  resultingOwnership = _out314;
                  readIdents = _1991_recIdents;
                }
              }
            }
          }
        }
        if (unmatched107) {
          DAST._IType _04 = _source107.dtor__0;
          if (_04.is_Passthrough) {
            DAST._IType _14 = _source107.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h77 = _14.dtor_Primitive_a0;
              if (_h77.is_Int) {
                unmatched107 = false;
                {
                  RAST._IType _1992_rhsType;
                  RAST._IType _out315;
                  _out315 = (this).GenType(_1969_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1992_rhsType = _out315;
                  RAST._IExpr _1993_recursiveGen;
                  DCOMP._IOwnership _1994___v143;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1995_recIdents;
                  RAST._IExpr _out316;
                  DCOMP._IOwnership _out317;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out318;
                  (this).GenExpr(_1968_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out316, out _out317, out _out318);
                  _1993_recursiveGen = _out316;
                  _1994___v143 = _out317;
                  _1995_recIdents = _out318;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1993_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out319;
                  DCOMP._IOwnership _out320;
                  (this).FromOwned(r, expectedOwnership, out _out319, out _out320);
                  r = _out319;
                  resultingOwnership = _out320;
                  readIdents = _1995_recIdents;
                }
              }
            }
          }
        }
        if (unmatched107) {
          DAST._IType _05 = _source107.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h78 = _05.dtor_Primitive_a0;
            if (_h78.is_Int) {
              DAST._IType _15 = _source107.dtor__1;
              if (_15.is_Primitive) {
                DAST._IPrimitive _h79 = _15.dtor_Primitive_a0;
                if (_h79.is_Char) {
                  unmatched107 = false;
                  {
                    RAST._IType _1996_rhsType;
                    RAST._IType _out321;
                    _out321 = (this).GenType(_1970_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1996_rhsType = _out321;
                    RAST._IExpr _1997_recursiveGen;
                    DCOMP._IOwnership _1998___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1999_recIdents;
                    RAST._IExpr _out322;
                    DCOMP._IOwnership _out323;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out324;
                    (this).GenExpr(_1968_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out322, out _out323, out _out324);
                    _1997_recursiveGen = _out322;
                    _1998___v144 = _out323;
                    _1999_recIdents = _out324;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1997_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out325;
                    DCOMP._IOwnership _out326;
                    (this).FromOwned(r, expectedOwnership, out _out325, out _out326);
                    r = _out325;
                    resultingOwnership = _out326;
                    readIdents = _1999_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched107) {
          DAST._IType _06 = _source107.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h710 = _06.dtor_Primitive_a0;
            if (_h710.is_Char) {
              DAST._IType _16 = _source107.dtor__1;
              if (_16.is_Primitive) {
                DAST._IPrimitive _h711 = _16.dtor_Primitive_a0;
                if (_h711.is_Int) {
                  unmatched107 = false;
                  {
                    RAST._IType _2000_rhsType;
                    RAST._IType _out327;
                    _out327 = (this).GenType(_1969_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _2000_rhsType = _out327;
                    RAST._IExpr _2001_recursiveGen;
                    DCOMP._IOwnership _2002___v145;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2003_recIdents;
                    RAST._IExpr _out328;
                    DCOMP._IOwnership _out329;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out330;
                    (this).GenExpr(_1968_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out328, out _out329, out _out330);
                    _2001_recursiveGen = _out328;
                    _2002___v145 = _out329;
                    _2003_recIdents = _out330;
                    r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1((_2001_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out331;
                    DCOMP._IOwnership _out332;
                    (this).FromOwned(r, expectedOwnership, out _out331, out _out332);
                    r = _out331;
                    resultingOwnership = _out332;
                    readIdents = _2003_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched107) {
          DAST._IType _07 = _source107.dtor__0;
          if (_07.is_Passthrough) {
            DAST._IType _17 = _source107.dtor__1;
            if (_17.is_Passthrough) {
              unmatched107 = false;
              {
                RAST._IExpr _2004_recursiveGen;
                DCOMP._IOwnership _2005___v148;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2006_recIdents;
                RAST._IExpr _out333;
                DCOMP._IOwnership _out334;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out335;
                (this).GenExpr(_1968_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out333, out _out334, out _out335);
                _2004_recursiveGen = _out333;
                _2005___v148 = _out334;
                _2006_recIdents = _out335;
                RAST._IType _2007_toTpeGen;
                RAST._IType _out336;
                _out336 = (this).GenType(_1970_toTpe, DCOMP.GenTypeContext.InBinding());
                _2007_toTpeGen = _out336;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_2004_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_2007_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out337;
                DCOMP._IOwnership _out338;
                (this).FromOwned(r, expectedOwnership, out _out337, out _out338);
                r = _out337;
                resultingOwnership = _out338;
                readIdents = _2006_recIdents;
              }
            }
          }
        }
        if (unmatched107) {
          unmatched107 = false;
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
      Std.Wrappers._IOption<RAST._IType> _2008_tpe;
      _2008_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _2009_placeboOpt;
      _2009_placeboOpt = (((_2008_tpe).is_Some) ? (((_2008_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _2010_currentlyBorrowed;
      _2010_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _2011_noNeedOfClone;
      _2011_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_2009_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _2010_currentlyBorrowed = false;
        _2011_noNeedOfClone = true;
        _2008_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_2009_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_2010_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_2008_tpe).is_Some) && (((_2008_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _2012_needObjectFromRef;
        _2012_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source108 = (selfIdent).dtor_dafnyType;
          bool unmatched108 = true;
          if (unmatched108) {
            if (_source108.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source108.dtor_resolved;
              DAST._IResolvedTypeBase _2013_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _2014_attributes = resolved4.dtor_attributes;
              unmatched108 = false;
              return ((_2013_base).is_Class) || ((_2013_base).is_Trait);
            }
          }
          if (unmatched108) {
            unmatched108 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_2012_needObjectFromRef) {
          r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_2011_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_2011_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_2010_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_2008_tpe).is_Some) && (((_2008_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_2015_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_2015_attributes).UniqueElements, false, (((_exists_var_2) => {
        DAST._IAttribute _2016_attribute = (DAST._IAttribute)_exists_var_2;
        return ((_2015_attributes).Contains(_2016_attribute)) && ((((_2016_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_2016_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      Dafny.ISequence<DAST._IFormal> _2017_signature;
      _2017_signature = (((name).is_CallName) ? ((((((name).dtor_receiverArg).is_Some) && ((name).dtor_receiverAsArgument)) ? (Dafny.Sequence<DAST._IFormal>.Concat(Dafny.Sequence<DAST._IFormal>.FromElements(((name).dtor_receiverArg).dtor_value), ((name).dtor_signature))) : (((name).dtor_signature)))) : (Dafny.Sequence<DAST._IFormal>.FromElements()));
      BigInteger _hi38 = new BigInteger((args).Count);
      for (BigInteger _2018_i = BigInteger.Zero; _2018_i < _hi38; _2018_i++) {
        DCOMP._IOwnership _2019_argOwnership;
        _2019_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if ((_2018_i) < (new BigInteger((_2017_signature).Count))) {
          RAST._IType _2020_tpe;
          RAST._IType _out342;
          _out342 = (this).GenType(((_2017_signature).Select(_2018_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _2020_tpe = _out342;
          if ((_2020_tpe).CanReadWithoutClone()) {
            _2019_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _2021_argExpr;
        DCOMP._IOwnership _2022___v155;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2023_argIdents;
        RAST._IExpr _out343;
        DCOMP._IOwnership _out344;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out345;
        (this).GenExpr((args).Select(_2018_i), selfIdent, env, _2019_argOwnership, out _out343, out _out344, out _out345);
        _2021_argExpr = _out343;
        _2022___v155 = _out344;
        _2023_argIdents = _out345;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2021_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2023_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi39 = new BigInteger((typeArgs).Count);
      for (BigInteger _2024_typeI = BigInteger.Zero; _2024_typeI < _hi39; _2024_typeI++) {
        RAST._IType _2025_typeExpr;
        RAST._IType _out346;
        _out346 = (this).GenType((typeArgs).Select(_2024_typeI), DCOMP.GenTypeContext.@default());
        _2025_typeExpr = _out346;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2025_typeExpr));
      }
      DAST._ICallName _source109 = name;
      bool unmatched109 = true;
      if (unmatched109) {
        if (_source109.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _2026_nameIdent = _source109.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType1 = _source109.dtor_onType;
          if (onType1.is_Some) {
            DAST._IType value10 = onType1.dtor_value;
            if (value10.is_UserDefined) {
              DAST._IResolvedType _2027_resolvedType = value10.dtor_resolved;
              unmatched109 = false;
              if ((((_2027_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_2028_resolvedType, _2029_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.SingleValue<Dafny.ISequence<Dafny.Rune>>(_2029_nameIdent), true, (((_forall_var_8) => {
                Dafny.ISequence<Dafny.Rune> _2030_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                return !(((_2028_resolvedType).dtor_properMethods).Contains(_2030_m)) || (!object.Equals(_2030_m, _2029_nameIdent));
              }))))(_2027_resolvedType, _2026_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_2027_resolvedType, (_2026_nameIdent)), _2027_resolvedType));
              } else {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
              }
            }
          }
        }
      }
      if (unmatched109) {
        unmatched109 = false;
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
      if ((((((fullNameQualifier).is_Some) && ((selfIdent).is_ThisTyped)) && (((selfIdent).dtor_dafnyType).is_UserDefined)) && ((this).IsSameResolvedType(((selfIdent).dtor_dafnyType).dtor_resolved, (fullNameQualifier).dtor_value))) && (!((this).HasExternAttributeRenamingModule(((fullNameQualifier).dtor_value).dtor_attributes)))) {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    }
    public Dafny.ISequence<Dafny.Rune> GetMethodName(DAST._IExpression @on, DAST._ICallName name)
    {
      var _pat_let_tv199 = @on;
      DAST._ICallName _source110 = name;
      bool unmatched110 = true;
      if (unmatched110) {
        if (_source110.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _2031_ident = _source110.dtor_name;
          unmatched110 = false;
          if ((_pat_let_tv199).is_ExternCompanion) {
            return (_2031_ident);
          } else {
            return DCOMP.__default.escapeName(_2031_ident);
          }
        }
      }
      if (unmatched110) {
        bool disjunctiveMatch15 = false;
        if (_source110.is_MapBuilderAdd) {
          disjunctiveMatch15 = true;
        }
        if (_source110.is_SetBuilderAdd) {
          disjunctiveMatch15 = true;
        }
        if (disjunctiveMatch15) {
          unmatched110 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
        }
      }
      if (unmatched110) {
        bool disjunctiveMatch16 = false;
        disjunctiveMatch16 = true;
        disjunctiveMatch16 = true;
        if (disjunctiveMatch16) {
          unmatched110 = false;
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
      DAST._IExpression _source111 = e;
      bool unmatched111 = true;
      if (unmatched111) {
        if (_source111.is_Literal) {
          unmatched111 = false;
          RAST._IExpr _out347;
          DCOMP._IOwnership _out348;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out347, out _out348, out _out349);
          r = _out347;
          resultingOwnership = _out348;
          readIdents = _out349;
        }
      }
      if (unmatched111) {
        if (_source111.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _2032_name = _source111.dtor_name;
          unmatched111 = false;
          {
            RAST._IExpr _out350;
            DCOMP._IOwnership _out351;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out352;
            (this).GenIdent(DCOMP.__default.escapeVar(_2032_name), selfIdent, env, expectedOwnership, out _out350, out _out351, out _out352);
            r = _out350;
            resultingOwnership = _out351;
            readIdents = _out352;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_ExternCompanion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2033_path = _source111.dtor_ExternCompanion_a0;
          unmatched111 = false;
          {
            RAST._IExpr _out353;
            _out353 = DCOMP.COMP.GenPathExpr(_2033_path, false);
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
      if (unmatched111) {
        if (_source111.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2034_path = _source111.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _2035_typeArgs = _source111.dtor_typeArgs;
          unmatched111 = false;
          {
            RAST._IExpr _out356;
            _out356 = DCOMP.COMP.GenPathExpr(_2034_path, true);
            r = _out356;
            if ((new BigInteger((_2035_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _2036_typeExprs;
              _2036_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_2035_typeArgs).Count);
              for (BigInteger _2037_i = BigInteger.Zero; _2037_i < _hi40; _2037_i++) {
                RAST._IType _2038_typeExpr;
                RAST._IType _out357;
                _out357 = (this).GenType((_2035_typeArgs).Select(_2037_i), DCOMP.GenTypeContext.@default());
                _2038_typeExpr = _out357;
                _2036_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_2036_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2038_typeExpr));
              }
              r = (r).ApplyType(_2036_typeExprs);
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
      if (unmatched111) {
        if (_source111.is_InitializationValue) {
          DAST._IType _2039_typ = _source111.dtor_typ;
          unmatched111 = false;
          {
            RAST._IType _2040_typExpr;
            RAST._IType _out360;
            _out360 = (this).GenType(_2039_typ, DCOMP.GenTypeContext.@default());
            _2040_typExpr = _out360;
            if ((_2040_typExpr).IsObjectOrPointer()) {
              r = (_2040_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_2040_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
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
      if (unmatched111) {
        if (_source111.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _2041_values = _source111.dtor_Tuple_a0;
          unmatched111 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2042_exprs;
            _2042_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi41 = new BigInteger((_2041_values).Count);
            for (BigInteger _2043_i = BigInteger.Zero; _2043_i < _hi41; _2043_i++) {
              RAST._IExpr _2044_recursiveGen;
              DCOMP._IOwnership _2045___v165;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2046_recIdents;
              RAST._IExpr _out363;
              DCOMP._IOwnership _out364;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out365;
              (this).GenExpr((_2041_values).Select(_2043_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out363, out _out364, out _out365);
              _2044_recursiveGen = _out363;
              _2045___v165 = _out364;
              _2046_recIdents = _out365;
              _2042_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_2042_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2044_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2046_recIdents);
            }
            r = (((new BigInteger((_2041_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_2042_exprs)) : (RAST.__default.SystemTuple(_2042_exprs)));
            RAST._IExpr _out366;
            DCOMP._IOwnership _out367;
            (this).FromOwned(r, expectedOwnership, out _out366, out _out367);
            r = _out366;
            resultingOwnership = _out367;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2047_path = _source111.dtor_path;
          Dafny.ISequence<DAST._IType> _2048_typeArgs = _source111.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2049_args = _source111.dtor_args;
          unmatched111 = false;
          {
            RAST._IExpr _out368;
            _out368 = DCOMP.COMP.GenPathExpr(_2047_path, true);
            r = _out368;
            if ((new BigInteger((_2048_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _2050_typeExprs;
              _2050_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi42 = new BigInteger((_2048_typeArgs).Count);
              for (BigInteger _2051_i = BigInteger.Zero; _2051_i < _hi42; _2051_i++) {
                RAST._IType _2052_typeExpr;
                RAST._IType _out369;
                _out369 = (this).GenType((_2048_typeArgs).Select(_2051_i), DCOMP.GenTypeContext.@default());
                _2052_typeExpr = _out369;
                _2050_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_2050_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2052_typeExpr));
              }
              r = (r).ApplyType(_2050_typeExprs);
            }
            r = (r).FSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _2053_arguments;
            _2053_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi43 = new BigInteger((_2049_args).Count);
            for (BigInteger _2054_i = BigInteger.Zero; _2054_i < _hi43; _2054_i++) {
              RAST._IExpr _2055_recursiveGen;
              DCOMP._IOwnership _2056___v166;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2057_recIdents;
              RAST._IExpr _out370;
              DCOMP._IOwnership _out371;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out372;
              (this).GenExpr((_2049_args).Select(_2054_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out370, out _out371, out _out372);
              _2055_recursiveGen = _out370;
              _2056___v166 = _out371;
              _2057_recIdents = _out372;
              _2053_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2053_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2055_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2057_recIdents);
            }
            r = (r).Apply(_2053_arguments);
            RAST._IExpr _out373;
            DCOMP._IOwnership _out374;
            (this).FromOwned(r, expectedOwnership, out _out373, out _out374);
            r = _out373;
            resultingOwnership = _out374;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _2058_dims = _source111.dtor_dims;
          DAST._IType _2059_typ = _source111.dtor_typ;
          unmatched111 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_2058_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _2060_msg;
              _2060_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2060_msg);
              }
              r = RAST.Expr.create_RawExpr(_2060_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _2061_typeGen;
              RAST._IType _out375;
              _out375 = (this).GenType(_2059_typ, DCOMP.GenTypeContext.@default());
              _2061_typeGen = _out375;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _2062_dimExprs;
              _2062_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi44 = new BigInteger((_2058_dims).Count);
              for (BigInteger _2063_i = BigInteger.Zero; _2063_i < _hi44; _2063_i++) {
                RAST._IExpr _2064_recursiveGen;
                DCOMP._IOwnership _2065___v167;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2066_recIdents;
                RAST._IExpr _out376;
                DCOMP._IOwnership _out377;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out378;
                (this).GenExpr((_2058_dims).Select(_2063_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out376, out _out377, out _out378);
                _2064_recursiveGen = _out376;
                _2065___v167 = _out377;
                _2066_recIdents = _out378;
                _2062_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_2062_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_2064_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2066_recIdents);
              }
              if ((new BigInteger((_2058_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _2067_class__name;
                _2067_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_2058_dims).Count)));
                r = (((((RAST.__default.dafny__runtime).MSel(_2067_class__name)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2061_typeGen))).FSel((this).placebos__usize)).Apply(_2062_dimExprs);
              } else {
                r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2061_typeGen))).Apply(_2062_dimExprs);
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
      if (unmatched111) {
        if (_source111.is_ArrayIndexToInt) {
          DAST._IExpression _2068_underlying = _source111.dtor_value;
          unmatched111 = false;
          {
            RAST._IExpr _2069_recursiveGen;
            DCOMP._IOwnership _2070___v168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2071_recIdents;
            RAST._IExpr _out381;
            DCOMP._IOwnership _out382;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
            (this).GenExpr(_2068_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out381, out _out382, out _out383);
            _2069_recursiveGen = _out381;
            _2070___v168 = _out382;
            _2071_recIdents = _out383;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(_2069_recursiveGen);
            readIdents = _2071_recIdents;
            RAST._IExpr _out384;
            DCOMP._IOwnership _out385;
            (this).FromOwned(r, expectedOwnership, out _out384, out _out385);
            r = _out384;
            resultingOwnership = _out385;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_FinalizeNewArray) {
          DAST._IExpression _2072_underlying = _source111.dtor_value;
          DAST._IType _2073_typ = _source111.dtor_typ;
          unmatched111 = false;
          {
            RAST._IType _2074_tpe;
            RAST._IType _out386;
            _out386 = (this).GenType(_2073_typ, DCOMP.GenTypeContext.@default());
            _2074_tpe = _out386;
            RAST._IExpr _2075_recursiveGen;
            DCOMP._IOwnership _2076___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2077_recIdents;
            RAST._IExpr _out387;
            DCOMP._IOwnership _out388;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
            (this).GenExpr(_2072_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out387, out _out388, out _out389);
            _2075_recursiveGen = _out387;
            _2076___v169 = _out388;
            _2077_recIdents = _out389;
            readIdents = _2077_recIdents;
            if ((_2074_tpe).IsObjectOrPointer()) {
              RAST._IType _2078_t;
              _2078_t = (_2074_tpe).ObjectOrPointerUnderlying();
              if ((_2078_t).is_Array) {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).array__construct)).Apply1(_2075_recursiveGen);
              } else if ((_2078_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _2079_c;
                _2079_c = (_2078_t).MultiArrayClass();
                r = ((((RAST.__default.dafny__runtime).MSel(_2079_c)).AsExpr()).FSel((this).array__construct)).Apply1(_2075_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_2074_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_2074_tpe)._ToString(DCOMP.__default.IND)));
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
      if (unmatched111) {
        if (_source111.is_DatatypeValue) {
          DAST._IResolvedType _2080_datatypeType = _source111.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _2081_typeArgs = _source111.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _2082_variant = _source111.dtor_variant;
          bool _2083_isCo = _source111.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2084_values = _source111.dtor_contents;
          unmatched111 = false;
          {
            RAST._IExpr _out392;
            _out392 = DCOMP.COMP.GenPathExpr((_2080_datatypeType).dtor_path, true);
            r = _out392;
            Dafny.ISequence<RAST._IType> _2085_genTypeArgs;
            _2085_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi45 = new BigInteger((_2081_typeArgs).Count);
            for (BigInteger _2086_i = BigInteger.Zero; _2086_i < _hi45; _2086_i++) {
              RAST._IType _2087_typeExpr;
              RAST._IType _out393;
              _out393 = (this).GenType((_2081_typeArgs).Select(_2086_i), DCOMP.GenTypeContext.@default());
              _2087_typeExpr = _out393;
              _2085_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_2085_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_2087_typeExpr));
            }
            if ((new BigInteger((_2081_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_2085_genTypeArgs);
            }
            r = (r).FSel(DCOMP.__default.escapeName(_2082_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _2088_assignments;
            _2088_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi46 = new BigInteger((_2084_values).Count);
            for (BigInteger _2089_i = BigInteger.Zero; _2089_i < _hi46; _2089_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs69 = (_2084_values).Select(_2089_i);
              Dafny.ISequence<Dafny.Rune> _2090_name = _let_tmp_rhs69.dtor__0;
              DAST._IExpression _2091_value = _let_tmp_rhs69.dtor__1;
              if (_2083_isCo) {
                RAST._IExpr _2092_recursiveGen;
                DCOMP._IOwnership _2093___v170;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2094_recIdents;
                RAST._IExpr _out394;
                DCOMP._IOwnership _out395;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out396;
                (this).GenExpr(_2091_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out394, out _out395, out _out396);
                _2092_recursiveGen = _out394;
                _2093___v170 = _out395;
                _2094_recIdents = _out396;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2094_recIdents);
                Dafny.ISequence<Dafny.Rune> _2095_allReadCloned;
                _2095_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_2094_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _2096_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2094_recIdents).Elements) {
                    _2096_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                    if ((_2094_recIdents).Contains(_2096_next)) {
                      goto after__ASSIGN_SUCH_THAT_3;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4716)");
                after__ASSIGN_SUCH_THAT_3: ;
                  _2095_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2095_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _2096_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2096_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _2094_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2094_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2096_next));
                }
                Dafny.ISequence<Dafny.Rune> _2097_wasAssigned;
                _2097_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _2095_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_2092_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _2088_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2088_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_2090_name), RAST.Expr.create_RawExpr(_2097_wasAssigned))));
              } else {
                RAST._IExpr _2098_recursiveGen;
                DCOMP._IOwnership _2099___v171;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2100_recIdents;
                RAST._IExpr _out397;
                DCOMP._IOwnership _out398;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
                (this).GenExpr(_2091_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out397, out _out398, out _out399);
                _2098_recursiveGen = _out397;
                _2099___v171 = _out398;
                _2100_recIdents = _out399;
                _2088_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2088_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_2090_name), _2098_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2100_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _2088_assignments);
            if ((this).IsRcWrapped((_2080_datatypeType).dtor_attributes)) {
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
      if (unmatched111) {
        if (_source111.is_Convert) {
          unmatched111 = false;
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
      if (unmatched111) {
        if (_source111.is_SeqConstruct) {
          DAST._IExpression _2101_length = _source111.dtor_length;
          DAST._IExpression _2102_expr = _source111.dtor_elem;
          unmatched111 = false;
          {
            RAST._IExpr _2103_recursiveGen;
            DCOMP._IOwnership _2104___v175;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2105_recIdents;
            RAST._IExpr _out405;
            DCOMP._IOwnership _out406;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out407;
            (this).GenExpr(_2102_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out405, out _out406, out _out407);
            _2103_recursiveGen = _out405;
            _2104___v175 = _out406;
            _2105_recIdents = _out407;
            RAST._IExpr _2106_lengthGen;
            DCOMP._IOwnership _2107___v176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2108_lengthIdents;
            RAST._IExpr _out408;
            DCOMP._IOwnership _out409;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out410;
            (this).GenExpr(_2101_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out408, out _out409, out _out410);
            _2106_lengthGen = _out408;
            _2107___v176 = _out409;
            _2108_lengthIdents = _out410;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_2103_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_2106_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2105_recIdents, _2108_lengthIdents);
            RAST._IExpr _out411;
            DCOMP._IOwnership _out412;
            (this).FromOwned(r, expectedOwnership, out _out411, out _out412);
            r = _out411;
            resultingOwnership = _out412;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _2109_exprs = _source111.dtor_elements;
          DAST._IType _2110_typ = _source111.dtor_typ;
          unmatched111 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _2111_genTpe;
            RAST._IType _out413;
            _out413 = (this).GenType(_2110_typ, DCOMP.GenTypeContext.@default());
            _2111_genTpe = _out413;
            BigInteger _2112_i;
            _2112_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2113_args;
            _2113_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2112_i) < (new BigInteger((_2109_exprs).Count))) {
              RAST._IExpr _2114_recursiveGen;
              DCOMP._IOwnership _2115___v177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2116_recIdents;
              RAST._IExpr _out414;
              DCOMP._IOwnership _out415;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out416;
              (this).GenExpr((_2109_exprs).Select(_2112_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out414, out _out415, out _out416);
              _2114_recursiveGen = _out414;
              _2115___v177 = _out415;
              _2116_recIdents = _out416;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2116_recIdents);
              _2113_args = Dafny.Sequence<RAST._IExpr>.Concat(_2113_args, Dafny.Sequence<RAST._IExpr>.FromElements(_2114_recursiveGen));
              _2112_i = (_2112_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).AsExpr()).Apply(_2113_args);
            if ((new BigInteger((_2113_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType()).Apply1(_2111_genTpe));
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
      if (unmatched111) {
        if (_source111.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _2117_exprs = _source111.dtor_elements;
          unmatched111 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2118_generatedValues;
            _2118_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2119_i;
            _2119_i = BigInteger.Zero;
            while ((_2119_i) < (new BigInteger((_2117_exprs).Count))) {
              RAST._IExpr _2120_recursiveGen;
              DCOMP._IOwnership _2121___v178;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2122_recIdents;
              RAST._IExpr _out419;
              DCOMP._IOwnership _out420;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out421;
              (this).GenExpr((_2117_exprs).Select(_2119_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out419, out _out420, out _out421);
              _2120_recursiveGen = _out419;
              _2121___v178 = _out420;
              _2122_recIdents = _out421;
              _2118_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2118_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2120_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2122_recIdents);
              _2119_i = (_2119_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).AsExpr()).Apply(_2118_generatedValues);
            RAST._IExpr _out422;
            DCOMP._IOwnership _out423;
            (this).FromOwned(r, expectedOwnership, out _out422, out _out423);
            r = _out422;
            resultingOwnership = _out423;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _2123_exprs = _source111.dtor_elements;
          unmatched111 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2124_generatedValues;
            _2124_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2125_i;
            _2125_i = BigInteger.Zero;
            while ((_2125_i) < (new BigInteger((_2123_exprs).Count))) {
              RAST._IExpr _2126_recursiveGen;
              DCOMP._IOwnership _2127___v179;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2128_recIdents;
              RAST._IExpr _out424;
              DCOMP._IOwnership _out425;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out426;
              (this).GenExpr((_2123_exprs).Select(_2125_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out424, out _out425, out _out426);
              _2126_recursiveGen = _out424;
              _2127___v179 = _out425;
              _2128_recIdents = _out426;
              _2124_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2124_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2126_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2128_recIdents);
              _2125_i = (_2125_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).AsExpr()).Apply(_2124_generatedValues);
            RAST._IExpr _out427;
            DCOMP._IOwnership _out428;
            (this).FromOwned(r, expectedOwnership, out _out427, out _out428);
            r = _out427;
            resultingOwnership = _out428;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_ToMultiset) {
          DAST._IExpression _2129_expr = _source111.dtor_ToMultiset_a0;
          unmatched111 = false;
          {
            RAST._IExpr _2130_recursiveGen;
            DCOMP._IOwnership _2131___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2132_recIdents;
            RAST._IExpr _out429;
            DCOMP._IOwnership _out430;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out431;
            (this).GenExpr(_2129_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out429, out _out430, out _out431);
            _2130_recursiveGen = _out429;
            _2131___v180 = _out430;
            _2132_recIdents = _out431;
            r = ((_2130_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2132_recIdents;
            RAST._IExpr _out432;
            DCOMP._IOwnership _out433;
            (this).FromOwned(r, expectedOwnership, out _out432, out _out433);
            r = _out432;
            resultingOwnership = _out433;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2133_mapElems = _source111.dtor_mapElems;
          unmatched111 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _2134_generatedValues;
            _2134_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2135_i;
            _2135_i = BigInteger.Zero;
            while ((_2135_i) < (new BigInteger((_2133_mapElems).Count))) {
              RAST._IExpr _2136_recursiveGenKey;
              DCOMP._IOwnership _2137___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2138_recIdentsKey;
              RAST._IExpr _out434;
              DCOMP._IOwnership _out435;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
              (this).GenExpr(((_2133_mapElems).Select(_2135_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out434, out _out435, out _out436);
              _2136_recursiveGenKey = _out434;
              _2137___v181 = _out435;
              _2138_recIdentsKey = _out436;
              RAST._IExpr _2139_recursiveGenValue;
              DCOMP._IOwnership _2140___v182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2141_recIdentsValue;
              RAST._IExpr _out437;
              DCOMP._IOwnership _out438;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
              (this).GenExpr(((_2133_mapElems).Select(_2135_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out437, out _out438, out _out439);
              _2139_recursiveGenValue = _out437;
              _2140___v182 = _out438;
              _2141_recIdentsValue = _out439;
              _2134_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_2134_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_2136_recursiveGenKey, _2139_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2138_recIdentsKey), _2141_recIdentsValue);
              _2135_i = (_2135_i) + (BigInteger.One);
            }
            _2135_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2142_arguments;
            _2142_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2135_i) < (new BigInteger((_2134_generatedValues).Count))) {
              RAST._IExpr _2143_genKey;
              _2143_genKey = ((_2134_generatedValues).Select(_2135_i)).dtor__0;
              RAST._IExpr _2144_genValue;
              _2144_genValue = ((_2134_generatedValues).Select(_2135_i)).dtor__1;
              _2142_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2142_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _2143_genKey, _2144_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _2135_i = (_2135_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).AsExpr()).Apply(_2142_arguments);
            RAST._IExpr _out440;
            DCOMP._IOwnership _out441;
            (this).FromOwned(r, expectedOwnership, out _out440, out _out441);
            r = _out440;
            resultingOwnership = _out441;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_SeqUpdate) {
          DAST._IExpression _2145_expr = _source111.dtor_expr;
          DAST._IExpression _2146_index = _source111.dtor_indexExpr;
          DAST._IExpression _2147_value = _source111.dtor_value;
          unmatched111 = false;
          {
            RAST._IExpr _2148_exprR;
            DCOMP._IOwnership _2149___v183;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2150_exprIdents;
            RAST._IExpr _out442;
            DCOMP._IOwnership _out443;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out444;
            (this).GenExpr(_2145_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out442, out _out443, out _out444);
            _2148_exprR = _out442;
            _2149___v183 = _out443;
            _2150_exprIdents = _out444;
            RAST._IExpr _2151_indexR;
            DCOMP._IOwnership _2152_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2153_indexIdents;
            RAST._IExpr _out445;
            DCOMP._IOwnership _out446;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
            (this).GenExpr(_2146_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out445, out _out446, out _out447);
            _2151_indexR = _out445;
            _2152_indexOwnership = _out446;
            _2153_indexIdents = _out447;
            RAST._IExpr _2154_valueR;
            DCOMP._IOwnership _2155_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2156_valueIdents;
            RAST._IExpr _out448;
            DCOMP._IOwnership _out449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out450;
            (this).GenExpr(_2147_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out448, out _out449, out _out450);
            _2154_valueR = _out448;
            _2155_valueOwnership = _out449;
            _2156_valueIdents = _out450;
            r = ((_2148_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2151_indexR, _2154_valueR));
            RAST._IExpr _out451;
            DCOMP._IOwnership _out452;
            (this).FromOwned(r, expectedOwnership, out _out451, out _out452);
            r = _out451;
            resultingOwnership = _out452;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2150_exprIdents, _2153_indexIdents), _2156_valueIdents);
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_MapUpdate) {
          DAST._IExpression _2157_expr = _source111.dtor_expr;
          DAST._IExpression _2158_index = _source111.dtor_indexExpr;
          DAST._IExpression _2159_value = _source111.dtor_value;
          unmatched111 = false;
          {
            RAST._IExpr _2160_exprR;
            DCOMP._IOwnership _2161___v184;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2162_exprIdents;
            RAST._IExpr _out453;
            DCOMP._IOwnership _out454;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out455;
            (this).GenExpr(_2157_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out453, out _out454, out _out455);
            _2160_exprR = _out453;
            _2161___v184 = _out454;
            _2162_exprIdents = _out455;
            RAST._IExpr _2163_indexR;
            DCOMP._IOwnership _2164_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2165_indexIdents;
            RAST._IExpr _out456;
            DCOMP._IOwnership _out457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out458;
            (this).GenExpr(_2158_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out456, out _out457, out _out458);
            _2163_indexR = _out456;
            _2164_indexOwnership = _out457;
            _2165_indexIdents = _out458;
            RAST._IExpr _2166_valueR;
            DCOMP._IOwnership _2167_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2168_valueIdents;
            RAST._IExpr _out459;
            DCOMP._IOwnership _out460;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out461;
            (this).GenExpr(_2159_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out459, out _out460, out _out461);
            _2166_valueR = _out459;
            _2167_valueOwnership = _out460;
            _2168_valueIdents = _out461;
            r = ((_2160_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2163_indexR, _2166_valueR));
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            (this).FromOwned(r, expectedOwnership, out _out462, out _out463);
            r = _out462;
            resultingOwnership = _out463;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2162_exprIdents, _2165_indexIdents), _2168_valueIdents);
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_This) {
          unmatched111 = false;
          {
            DCOMP._ISelfInfo _source112 = selfIdent;
            bool unmatched112 = true;
            if (unmatched112) {
              if (_source112.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _2169_id = _source112.dtor_rSelfName;
                DAST._IType _2170_dafnyType = _source112.dtor_dafnyType;
                unmatched112 = false;
                {
                  RAST._IExpr _out464;
                  DCOMP._IOwnership _out465;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
                  (this).GenIdent(_2169_id, selfIdent, env, expectedOwnership, out _out464, out _out465, out _out466);
                  r = _out464;
                  resultingOwnership = _out465;
                  readIdents = _out466;
                }
              }
            }
            if (unmatched112) {
              DCOMP._ISelfInfo _2171_None = _source112;
              unmatched112 = false;
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
      if (unmatched111) {
        if (_source111.is_Ite) {
          DAST._IExpression _2172_cond = _source111.dtor_cond;
          DAST._IExpression _2173_t = _source111.dtor_thn;
          DAST._IExpression _2174_f = _source111.dtor_els;
          unmatched111 = false;
          {
            RAST._IExpr _2175_cond;
            DCOMP._IOwnership _2176___v185;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2177_recIdentsCond;
            RAST._IExpr _out469;
            DCOMP._IOwnership _out470;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out471;
            (this).GenExpr(_2172_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out469, out _out470, out _out471);
            _2175_cond = _out469;
            _2176___v185 = _out470;
            _2177_recIdentsCond = _out471;
            RAST._IExpr _2178_fExpr;
            DCOMP._IOwnership _2179_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2180_recIdentsF;
            RAST._IExpr _out472;
            DCOMP._IOwnership _out473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
            (this).GenExpr(_2174_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out472, out _out473, out _out474);
            _2178_fExpr = _out472;
            _2179_fOwned = _out473;
            _2180_recIdentsF = _out474;
            RAST._IExpr _2181_tExpr;
            DCOMP._IOwnership _2182___v186;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2183_recIdentsT;
            RAST._IExpr _out475;
            DCOMP._IOwnership _out476;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out477;
            (this).GenExpr(_2173_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out475, out _out476, out _out477);
            _2181_tExpr = _out475;
            _2182___v186 = _out476;
            _2183_recIdentsT = _out477;
            r = RAST.Expr.create_IfExpr(_2175_cond, _2181_tExpr, _2178_fExpr);
            RAST._IExpr _out478;
            DCOMP._IOwnership _out479;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out478, out _out479);
            r = _out478;
            resultingOwnership = _out479;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2177_recIdentsCond, _2183_recIdentsT), _2180_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source111.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _2184_e = _source111.dtor_expr;
            DAST.Format._IUnaryOpFormat _2185_format = _source111.dtor_format1;
            unmatched111 = false;
            {
              RAST._IExpr _2186_recursiveGen;
              DCOMP._IOwnership _2187___v187;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2188_recIdents;
              RAST._IExpr _out480;
              DCOMP._IOwnership _out481;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out482;
              (this).GenExpr(_2184_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out480, out _out481, out _out482);
              _2186_recursiveGen = _out480;
              _2187___v187 = _out481;
              _2188_recIdents = _out482;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _2186_recursiveGen, _2185_format);
              RAST._IExpr _out483;
              DCOMP._IOwnership _out484;
              (this).FromOwned(r, expectedOwnership, out _out483, out _out484);
              r = _out483;
              resultingOwnership = _out484;
              readIdents = _2188_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source111.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _2189_e = _source111.dtor_expr;
            DAST.Format._IUnaryOpFormat _2190_format = _source111.dtor_format1;
            unmatched111 = false;
            {
              RAST._IExpr _2191_recursiveGen;
              DCOMP._IOwnership _2192___v188;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2193_recIdents;
              RAST._IExpr _out485;
              DCOMP._IOwnership _out486;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out487;
              (this).GenExpr(_2189_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out485, out _out486, out _out487);
              _2191_recursiveGen = _out485;
              _2192___v188 = _out486;
              _2193_recIdents = _out487;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _2191_recursiveGen, _2190_format);
              RAST._IExpr _out488;
              DCOMP._IOwnership _out489;
              (this).FromOwned(r, expectedOwnership, out _out488, out _out489);
              r = _out488;
              resultingOwnership = _out489;
              readIdents = _2193_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source111.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _2194_e = _source111.dtor_expr;
            DAST.Format._IUnaryOpFormat _2195_format = _source111.dtor_format1;
            unmatched111 = false;
            {
              RAST._IExpr _2196_recursiveGen;
              DCOMP._IOwnership _2197_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2198_recIdents;
              RAST._IExpr _out490;
              DCOMP._IOwnership _out491;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out492;
              (this).GenExpr(_2194_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out490, out _out491, out _out492);
              _2196_recursiveGen = _out490;
              _2197_recOwned = _out491;
              _2198_recIdents = _out492;
              r = ((_2196_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out493;
              DCOMP._IOwnership _out494;
              (this).FromOwned(r, expectedOwnership, out _out493, out _out494);
              r = _out493;
              resultingOwnership = _out494;
              readIdents = _2198_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_BinOp) {
          unmatched111 = false;
          RAST._IExpr _out495;
          DCOMP._IOwnership _out496;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out497;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out495, out _out496, out _out497);
          r = _out495;
          resultingOwnership = _out496;
          readIdents = _out497;
        }
      }
      if (unmatched111) {
        if (_source111.is_ArrayLen) {
          DAST._IExpression _2199_expr = _source111.dtor_expr;
          DAST._IType _2200_exprType = _source111.dtor_exprType;
          BigInteger _2201_dim = _source111.dtor_dim;
          bool _2202_native = _source111.dtor_native;
          unmatched111 = false;
          {
            RAST._IExpr _2203_recursiveGen;
            DCOMP._IOwnership _2204___v193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2205_recIdents;
            RAST._IExpr _out498;
            DCOMP._IOwnership _out499;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
            (this).GenExpr(_2199_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out498, out _out499, out _out500);
            _2203_recursiveGen = _out498;
            _2204___v193 = _out499;
            _2205_recIdents = _out500;
            RAST._IType _2206_arrayType;
            RAST._IType _out501;
            _out501 = (this).GenType(_2200_exprType, DCOMP.GenTypeContext.@default());
            _2206_arrayType = _out501;
            if (!((_2206_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2207_msg;
              _2207_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2206_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2207_msg);
              r = RAST.Expr.create_RawExpr(_2207_msg);
            } else {
              RAST._IType _2208_underlying;
              _2208_underlying = (_2206_arrayType).ObjectOrPointerUnderlying();
              if (((_2201_dim).Sign == 0) && ((_2208_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2203_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2201_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2203_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_2203_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_2201_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_2202_native)) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(r);
              }
            }
            RAST._IExpr _out502;
            DCOMP._IOwnership _out503;
            (this).FromOwned(r, expectedOwnership, out _out502, out _out503);
            r = _out502;
            resultingOwnership = _out503;
            readIdents = _2205_recIdents;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_MapKeys) {
          DAST._IExpression _2209_expr = _source111.dtor_expr;
          unmatched111 = false;
          {
            RAST._IExpr _2210_recursiveGen;
            DCOMP._IOwnership _2211___v194;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2212_recIdents;
            RAST._IExpr _out504;
            DCOMP._IOwnership _out505;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out506;
            (this).GenExpr(_2209_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out504, out _out505, out _out506);
            _2210_recursiveGen = _out504;
            _2211___v194 = _out505;
            _2212_recIdents = _out506;
            readIdents = _2212_recIdents;
            r = ((_2210_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out507;
            DCOMP._IOwnership _out508;
            (this).FromOwned(r, expectedOwnership, out _out507, out _out508);
            r = _out507;
            resultingOwnership = _out508;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_MapValues) {
          DAST._IExpression _2213_expr = _source111.dtor_expr;
          unmatched111 = false;
          {
            RAST._IExpr _2214_recursiveGen;
            DCOMP._IOwnership _2215___v195;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2216_recIdents;
            RAST._IExpr _out509;
            DCOMP._IOwnership _out510;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out511;
            (this).GenExpr(_2213_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out509, out _out510, out _out511);
            _2214_recursiveGen = _out509;
            _2215___v195 = _out510;
            _2216_recIdents = _out511;
            readIdents = _2216_recIdents;
            r = ((_2214_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out512;
            DCOMP._IOwnership _out513;
            (this).FromOwned(r, expectedOwnership, out _out512, out _out513);
            r = _out512;
            resultingOwnership = _out513;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_MapItems) {
          DAST._IExpression _2217_expr = _source111.dtor_expr;
          unmatched111 = false;
          {
            RAST._IExpr _2218_recursiveGen;
            DCOMP._IOwnership _2219___v196;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2220_recIdents;
            RAST._IExpr _out514;
            DCOMP._IOwnership _out515;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out516;
            (this).GenExpr(_2217_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out514, out _out515, out _out516);
            _2218_recursiveGen = _out514;
            _2219___v196 = _out515;
            _2220_recIdents = _out516;
            readIdents = _2220_recIdents;
            r = ((_2218_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("items"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out517;
            DCOMP._IOwnership _out518;
            (this).FromOwned(r, expectedOwnership, out _out517, out _out518);
            r = _out517;
            resultingOwnership = _out518;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_SelectFn) {
          DAST._IExpression _2221_on = _source111.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2222_field = _source111.dtor_field;
          bool _2223_isDatatype = _source111.dtor_onDatatype;
          bool _2224_isStatic = _source111.dtor_isStatic;
          bool _2225_isConstant = _source111.dtor_isConstant;
          Dafny.ISequence<DAST._IType> _2226_arguments = _source111.dtor_arguments;
          unmatched111 = false;
          {
            RAST._IExpr _2227_onExpr;
            DCOMP._IOwnership _2228_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2229_recIdents;
            RAST._IExpr _out519;
            DCOMP._IOwnership _out520;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
            (this).GenExpr(_2221_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out519, out _out520, out _out521);
            _2227_onExpr = _out519;
            _2228_onOwned = _out520;
            _2229_recIdents = _out521;
            Dafny.ISequence<Dafny.Rune> _2230_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2231_onString;
            _2231_onString = (_2227_onExpr)._ToString(DCOMP.__default.IND);
            if (_2224_isStatic) {
              DCOMP._IEnvironment _2232_lEnv;
              _2232_lEnv = env;
              Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>> _2233_args;
              _2233_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements();
              _2230_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|");
              BigInteger _hi47 = new BigInteger((_2226_arguments).Count);
              for (BigInteger _2234_i = BigInteger.Zero; _2234_i < _hi47; _2234_i++) {
                if ((_2234_i).Sign == 1) {
                  _2230_s = Dafny.Sequence<Dafny.Rune>.Concat(_2230_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                RAST._IType _2235_ty;
                RAST._IType _out522;
                _out522 = (this).GenType((_2226_arguments).Select(_2234_i), DCOMP.GenTypeContext.@default());
                _2235_ty = _out522;
                RAST._IType _2236_bTy;
                _2236_bTy = RAST.Type.create_Borrowed(_2235_ty);
                Dafny.ISequence<Dafny.Rune> _2237_name;
                _2237_name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), Std.Strings.__default.OfInt(_2234_i));
                _2232_lEnv = (_2232_lEnv).AddAssigned(_2237_name, _2236_bTy);
                _2233_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.Concat(_2233_args, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>.create(_2237_name, _2235_ty)));
                _2230_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2230_s, _2237_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_2236_bTy)._ToString(DCOMP.__default.IND));
              }
              _2230_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2230_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| ")), _2231_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeVar(_2222_field)), ((_2225_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("));
              BigInteger _hi48 = new BigInteger((_2233_args).Count);
              for (BigInteger _2238_i = BigInteger.Zero; _2238_i < _hi48; _2238_i++) {
                if ((_2238_i).Sign == 1) {
                  _2230_s = Dafny.Sequence<Dafny.Rune>.Concat(_2230_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType> _let_tmp_rhs70 = (_2233_args).Select(_2238_i);
                Dafny.ISequence<Dafny.Rune> _2239_name = _let_tmp_rhs70.dtor__0;
                RAST._IType _2240_ty = _let_tmp_rhs70.dtor__1;
                RAST._IExpr _2241_rIdent;
                DCOMP._IOwnership _2242___v197;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2243___v198;
                RAST._IExpr _out523;
                DCOMP._IOwnership _out524;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
                (this).GenIdent(_2239_name, selfIdent, _2232_lEnv, (((_2240_ty).CanReadWithoutClone()) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed())), out _out523, out _out524, out _out525);
                _2241_rIdent = _out523;
                _2242___v197 = _out524;
                _2243___v198 = _out525;
                _2230_s = Dafny.Sequence<Dafny.Rune>.Concat(_2230_s, (_2241_rIdent)._ToString(DCOMP.__default.IND));
              }
              _2230_s = Dafny.Sequence<Dafny.Rune>.Concat(_2230_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            } else {
              _2230_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2230_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2230_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2231_onString), ((object.Equals(_2228_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2244_args;
              _2244_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2245_i;
              _2245_i = BigInteger.Zero;
              while ((_2245_i) < (new BigInteger((_2226_arguments).Count))) {
                if ((_2245_i).Sign == 1) {
                  _2244_args = Dafny.Sequence<Dafny.Rune>.Concat(_2244_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2244_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2244_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2245_i));
                _2245_i = (_2245_i) + (BigInteger.One);
              }
              _2230_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2230_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2244_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2230_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2230_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeVar(_2222_field)), ((_2225_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2244_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2230_s = Dafny.Sequence<Dafny.Rune>.Concat(_2230_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2230_s = Dafny.Sequence<Dafny.Rune>.Concat(_2230_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2246_typeShape;
            _2246_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2247_i;
            _2247_i = BigInteger.Zero;
            while ((_2247_i) < (new BigInteger((_2226_arguments).Count))) {
              if ((_2247_i).Sign == 1) {
                _2246_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2246_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2246_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2246_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2247_i = (_2247_i) + (BigInteger.One);
            }
            _2246_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2246_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2230_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2230_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2246_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2230_s);
            RAST._IExpr _out526;
            DCOMP._IOwnership _out527;
            (this).FromOwned(r, expectedOwnership, out _out526, out _out527);
            r = _out526;
            resultingOwnership = _out527;
            readIdents = _2229_recIdents;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_Select) {
          DAST._IExpression _2248_on = _source111.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2249_field = _source111.dtor_field;
          bool _2250_isConstant = _source111.dtor_isConstant;
          bool _2251_isDatatype = _source111.dtor_onDatatype;
          DAST._IType _2252_fieldType = _source111.dtor_fieldType;
          unmatched111 = false;
          {
            if (((_2248_on).is_Companion) || ((_2248_on).is_ExternCompanion)) {
              RAST._IExpr _2253_onExpr;
              DCOMP._IOwnership _2254_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2255_recIdents;
              RAST._IExpr _out528;
              DCOMP._IOwnership _out529;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
              (this).GenExpr(_2248_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out528, out _out529, out _out530);
              _2253_onExpr = _out528;
              _2254_onOwned = _out529;
              _2255_recIdents = _out530;
              r = ((_2253_onExpr).FSel(DCOMP.__default.escapeVar(_2249_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out531;
              DCOMP._IOwnership _out532;
              (this).FromOwned(r, expectedOwnership, out _out531, out _out532);
              r = _out531;
              resultingOwnership = _out532;
              readIdents = _2255_recIdents;
              return ;
            } else if (_2251_isDatatype) {
              RAST._IExpr _2256_onExpr;
              DCOMP._IOwnership _2257_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2258_recIdents;
              RAST._IExpr _out533;
              DCOMP._IOwnership _out534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
              (this).GenExpr(_2248_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out533, out _out534, out _out535);
              _2256_onExpr = _out533;
              _2257_onOwned = _out534;
              _2258_recIdents = _out535;
              r = ((_2256_onExpr).Sel(DCOMP.__default.escapeVar(_2249_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2259_typ;
              RAST._IType _out536;
              _out536 = (this).GenType(_2252_fieldType, DCOMP.GenTypeContext.@default());
              _2259_typ = _out536;
              RAST._IExpr _out537;
              DCOMP._IOwnership _out538;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out537, out _out538);
              r = _out537;
              resultingOwnership = _out538;
              readIdents = _2258_recIdents;
            } else {
              RAST._IExpr _2260_onExpr;
              DCOMP._IOwnership _2261_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2262_recIdents;
              RAST._IExpr _out539;
              DCOMP._IOwnership _out540;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
              (this).GenExpr(_2248_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out539, out _out540, out _out541);
              _2260_onExpr = _out539;
              _2261_onOwned = _out540;
              _2262_recIdents = _out541;
              r = _2260_onExpr;
              if (!object.Equals(_2260_onExpr, RAST.__default.self)) {
                RAST._IExpr _source113 = _2260_onExpr;
                bool unmatched113 = true;
                if (unmatched113) {
                  if (_source113.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source113.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source113.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name8 = underlying5.dtor_name;
                        if (object.Equals(name8, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          unmatched113 = false;
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                        }
                      }
                    }
                  }
                }
                if (unmatched113) {
                  unmatched113 = false;
                }
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeVar(_2249_field));
              if (_2250_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out542;
              DCOMP._IOwnership _out543;
              (this).FromOwned(r, expectedOwnership, out _out542, out _out543);
              r = _out542;
              resultingOwnership = _out543;
              readIdents = _2262_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_Index) {
          DAST._IExpression _2263_on = _source111.dtor_expr;
          DAST._ICollKind _2264_collKind = _source111.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2265_indices = _source111.dtor_indices;
          unmatched111 = false;
          {
            RAST._IExpr _2266_onExpr;
            DCOMP._IOwnership _2267_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2268_recIdents;
            RAST._IExpr _out544;
            DCOMP._IOwnership _out545;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out546;
            (this).GenExpr(_2263_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out544, out _out545, out _out546);
            _2266_onExpr = _out544;
            _2267_onOwned = _out545;
            _2268_recIdents = _out546;
            readIdents = _2268_recIdents;
            r = _2266_onExpr;
            bool _2269_hadArray;
            _2269_hadArray = false;
            if (object.Equals(_2264_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2269_hadArray = true;
              if ((new BigInteger((_2265_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi49 = new BigInteger((_2265_indices).Count);
            for (BigInteger _2270_i = BigInteger.Zero; _2270_i < _hi49; _2270_i++) {
              if (object.Equals(_2264_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2271_idx;
                DCOMP._IOwnership _2272_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2273_recIdentsIdx;
                RAST._IExpr _out547;
                DCOMP._IOwnership _out548;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
                (this).GenExpr((_2265_indices).Select(_2270_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out547, out _out548, out _out549);
                _2271_idx = _out547;
                _2272_idxOwned = _out548;
                _2273_recIdentsIdx = _out549;
                _2271_idx = RAST.__default.IntoUsize(_2271_idx);
                r = RAST.Expr.create_SelectIndex(r, _2271_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2273_recIdentsIdx);
              } else {
                RAST._IExpr _2274_idx;
                DCOMP._IOwnership _2275_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2276_recIdentsIdx;
                RAST._IExpr _out550;
                DCOMP._IOwnership _out551;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
                (this).GenExpr((_2265_indices).Select(_2270_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out550, out _out551, out _out552);
                _2274_idx = _out550;
                _2275_idxOwned = _out551;
                _2276_recIdentsIdx = _out552;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2274_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2276_recIdentsIdx);
              }
            }
            if (_2269_hadArray) {
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
      if (unmatched111) {
        if (_source111.is_IndexRange) {
          DAST._IExpression _2277_on = _source111.dtor_expr;
          bool _2278_isArray = _source111.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2279_low = _source111.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2280_high = _source111.dtor_high;
          unmatched111 = false;
          {
            RAST._IExpr _2281_onExpr;
            DCOMP._IOwnership _2282_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2283_recIdents;
            RAST._IExpr _out555;
            DCOMP._IOwnership _out556;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
            (this).GenExpr(_2277_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out555, out _out556, out _out557);
            _2281_onExpr = _out555;
            _2282_onOwned = _out556;
            _2283_recIdents = _out557;
            readIdents = _2283_recIdents;
            Dafny.ISequence<Dafny.Rune> _2284_methodName;
            _2284_methodName = (((_2279_low).is_Some) ? ((((_2280_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2280_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2285_arguments;
            _2285_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source114 = _2279_low;
            bool unmatched114 = true;
            if (unmatched114) {
              if (_source114.is_Some) {
                DAST._IExpression _2286_l = _source114.dtor_value;
                unmatched114 = false;
                {
                  RAST._IExpr _2287_lExpr;
                  DCOMP._IOwnership _2288___v201;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2289_recIdentsL;
                  RAST._IExpr _out558;
                  DCOMP._IOwnership _out559;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
                  (this).GenExpr(_2286_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out558, out _out559, out _out560);
                  _2287_lExpr = _out558;
                  _2288___v201 = _out559;
                  _2289_recIdentsL = _out560;
                  _2285_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2285_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2287_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2289_recIdentsL);
                }
              }
            }
            if (unmatched114) {
              unmatched114 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source115 = _2280_high;
            bool unmatched115 = true;
            if (unmatched115) {
              if (_source115.is_Some) {
                DAST._IExpression _2290_h = _source115.dtor_value;
                unmatched115 = false;
                {
                  RAST._IExpr _2291_hExpr;
                  DCOMP._IOwnership _2292___v202;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2293_recIdentsH;
                  RAST._IExpr _out561;
                  DCOMP._IOwnership _out562;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
                  (this).GenExpr(_2290_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out561, out _out562, out _out563);
                  _2291_hExpr = _out561;
                  _2292___v202 = _out562;
                  _2293_recIdentsH = _out563;
                  _2285_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2285_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2291_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2293_recIdentsH);
                }
              }
            }
            if (unmatched115) {
              unmatched115 = false;
            }
            r = _2281_onExpr;
            if (_2278_isArray) {
              if (!(_2284_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2284_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2284_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).FSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2284_methodName))).Apply(_2285_arguments);
            } else {
              if (!(_2284_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2284_methodName)).Apply(_2285_arguments);
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
      if (unmatched111) {
        if (_source111.is_TupleSelect) {
          DAST._IExpression _2294_on = _source111.dtor_expr;
          BigInteger _2295_idx = _source111.dtor_index;
          DAST._IType _2296_fieldType = _source111.dtor_fieldType;
          unmatched111 = false;
          {
            RAST._IExpr _2297_onExpr;
            DCOMP._IOwnership _2298_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2299_recIdents;
            RAST._IExpr _out566;
            DCOMP._IOwnership _out567;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
            (this).GenExpr(_2294_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out566, out _out567, out _out568);
            _2297_onExpr = _out566;
            _2298_onOwnership = _out567;
            _2299_recIdents = _out568;
            Dafny.ISequence<Dafny.Rune> _2300_selName;
            _2300_selName = Std.Strings.__default.OfNat(_2295_idx);
            DAST._IType _source116 = _2296_fieldType;
            bool unmatched116 = true;
            if (unmatched116) {
              if (_source116.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2301_tps = _source116.dtor_Tuple_a0;
                unmatched116 = false;
                if (((_2296_fieldType).is_Tuple) && ((new BigInteger((_2301_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2300_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2300_selName);
                }
              }
            }
            if (unmatched116) {
              unmatched116 = false;
            }
            r = ((_2297_onExpr).Sel(_2300_selName)).Clone();
            RAST._IExpr _out569;
            DCOMP._IOwnership _out570;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out569, out _out570);
            r = _out569;
            resultingOwnership = _out570;
            readIdents = _2299_recIdents;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_Call) {
          DAST._IExpression _2302_on = _source111.dtor_on;
          DAST._ICallName _2303_name = _source111.dtor_callName;
          Dafny.ISequence<DAST._IType> _2304_typeArgs = _source111.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2305_args = _source111.dtor_args;
          unmatched111 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2306_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2307_recIdents;
            Dafny.ISequence<RAST._IType> _2308_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2309_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out571;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out572;
            Dafny.ISequence<RAST._IType> _out573;
            Std.Wrappers._IOption<DAST._IResolvedType> _out574;
            (this).GenArgs(selfIdent, _2303_name, _2304_typeArgs, _2305_args, env, out _out571, out _out572, out _out573, out _out574);
            _2306_argExprs = _out571;
            _2307_recIdents = _out572;
            _2308_typeExprs = _out573;
            _2309_fullNameQualifier = _out574;
            readIdents = _2307_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source117 = _2309_fullNameQualifier;
            bool unmatched117 = true;
            if (unmatched117) {
              if (_source117.is_Some) {
                DAST._IResolvedType value11 = _source117.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2310_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2311_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2312_base = value11.dtor_kind;
                unmatched117 = false;
                RAST._IExpr _2313_fullPath;
                RAST._IExpr _out575;
                _out575 = DCOMP.COMP.GenPathExpr(_2310_path, true);
                _2313_fullPath = _out575;
                Dafny.ISequence<RAST._IType> _2314_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out576;
                _out576 = (this).GenTypeArgs(_2311_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2314_onTypeExprs = _out576;
                RAST._IExpr _2315_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2316_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2317_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2312_base).is_Trait) || ((_2312_base).is_Class)) {
                  RAST._IExpr _out577;
                  DCOMP._IOwnership _out578;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out579;
                  (this).GenExpr(_2302_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out577, out _out578, out _out579);
                  _2315_onExpr = _out577;
                  _2316_recOwnership = _out578;
                  _2317_recIdents = _out579;
                  _2315_onExpr = ((this).read__macro).Apply1(_2315_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2317_recIdents);
                } else {
                  RAST._IExpr _out580;
                  DCOMP._IOwnership _out581;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out582;
                  (this).GenExpr(_2302_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out580, out _out581, out _out582);
                  _2315_onExpr = _out580;
                  _2316_recOwnership = _out581;
                  _2317_recIdents = _out582;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2317_recIdents);
                }
                r = ((((_2313_fullPath).ApplyType(_2314_onTypeExprs)).FSel(DCOMP.__default.escapeName((_2303_name).dtor_name))).ApplyType(_2308_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2315_onExpr), _2306_argExprs));
                RAST._IExpr _out583;
                DCOMP._IOwnership _out584;
                (this).FromOwned(r, expectedOwnership, out _out583, out _out584);
                r = _out583;
                resultingOwnership = _out584;
              }
            }
            if (unmatched117) {
              unmatched117 = false;
              RAST._IExpr _2318_onExpr;
              DCOMP._IOwnership _2319___v208;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2320_recIdents;
              RAST._IExpr _out585;
              DCOMP._IOwnership _out586;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out587;
              (this).GenExpr(_2302_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out585, out _out586, out _out587);
              _2318_onExpr = _out585;
              _2319___v208 = _out586;
              _2320_recIdents = _out587;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2320_recIdents);
              Dafny.ISequence<Dafny.Rune> _2321_renderedName;
              _2321_renderedName = (this).GetMethodName(_2302_on, _2303_name);
              DAST._IExpression _source118 = _2302_on;
              bool unmatched118 = true;
              if (unmatched118) {
                bool disjunctiveMatch17 = false;
                if (_source118.is_Companion) {
                  disjunctiveMatch17 = true;
                }
                if (_source118.is_ExternCompanion) {
                  disjunctiveMatch17 = true;
                }
                if (disjunctiveMatch17) {
                  unmatched118 = false;
                  {
                    _2318_onExpr = (_2318_onExpr).FSel(_2321_renderedName);
                  }
                }
              }
              if (unmatched118) {
                unmatched118 = false;
                {
                  if (!object.Equals(_2318_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source119 = _2303_name;
                    bool unmatched119 = true;
                    if (unmatched119) {
                      if (_source119.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source119.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2322_tpe = onType2.dtor_value;
                          unmatched119 = false;
                          RAST._IType _2323_typ;
                          RAST._IType _out588;
                          _out588 = (this).GenType(_2322_tpe, DCOMP.GenTypeContext.@default());
                          _2323_typ = _out588;
                          if ((_2323_typ).IsObjectOrPointer()) {
                            _2318_onExpr = ((this).read__macro).Apply1(_2318_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched119) {
                      unmatched119 = false;
                    }
                  }
                  _2318_onExpr = (_2318_onExpr).Sel(_2321_renderedName);
                }
              }
              r = ((_2318_onExpr).ApplyType(_2308_typeExprs)).Apply(_2306_argExprs);
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
      if (unmatched111) {
        if (_source111.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2324_paramsDafny = _source111.dtor_params;
          DAST._IType _2325_retType = _source111.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2326_body = _source111.dtor_body;
          unmatched111 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2327_params;
            Dafny.ISequence<RAST._IFormal> _out591;
            _out591 = (this).GenParams(_2324_paramsDafny, true);
            _2327_params = _out591;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2328_paramNames;
            _2328_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2329_paramTypesMap;
            _2329_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi50 = new BigInteger((_2327_params).Count);
            for (BigInteger _2330_i = BigInteger.Zero; _2330_i < _hi50; _2330_i++) {
              Dafny.ISequence<Dafny.Rune> _2331_name;
              _2331_name = ((_2327_params).Select(_2330_i)).dtor_name;
              _2328_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2328_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2331_name));
              _2329_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2329_paramTypesMap, _2331_name, ((_2327_params).Select(_2330_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2332_subEnv;
            _2332_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2328_paramNames, _2329_paramTypesMap));
            RAST._IExpr _2333_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2334_recIdents;
            DCOMP._IEnvironment _2335___v218;
            RAST._IExpr _out592;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out593;
            DCOMP._IEnvironment _out594;
            (this).GenStmts(_2326_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2332_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out592, out _out593, out _out594);
            _2333_recursiveGen = _out592;
            _2334_recIdents = _out593;
            _2335___v218 = _out594;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2334_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2334_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2336_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll9 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_10 in (_2336_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2337_name = (Dafny.ISequence<Dafny.Rune>)_compr_10;
                if ((_2336_paramNames).Contains(_2337_name)) {
                  _coll9.Add(_2337_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll9);
            }))())(_2328_paramNames));
            RAST._IExpr _2338_allReadCloned;
            _2338_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2334_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2339_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_4 in (_2334_recIdents).Elements) {
                _2339_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_4;
                if ((_2334_recIdents).Contains(_2339_next)) {
                  goto after__ASSIGN_SUCH_THAT_4;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 5218)");
            after__ASSIGN_SUCH_THAT_4: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2339_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2340_selfCloned;
                DCOMP._IOwnership _2341___v219;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2342___v220;
                RAST._IExpr _out595;
                DCOMP._IOwnership _out596;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out597;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out595, out _out596, out _out597);
                _2340_selfCloned = _out595;
                _2341___v219 = _out596;
                _2342___v220 = _out597;
                _2338_allReadCloned = (_2338_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2340_selfCloned)));
              } else if (!((_2328_paramNames).Contains(_2339_next))) {
                RAST._IExpr _2343_copy;
                _2343_copy = (RAST.Expr.create_Identifier(_2339_next)).Clone();
                _2338_allReadCloned = (_2338_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2339_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2343_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2339_next));
              }
              _2334_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2334_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2339_next));
            }
            RAST._IType _2344_retTypeGen;
            RAST._IType _out598;
            _out598 = (this).GenType(_2325_retType, DCOMP.GenTypeContext.InFn());
            _2344_retTypeGen = _out598;
            r = RAST.Expr.create_Block((_2338_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2327_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2344_retTypeGen), RAST.Expr.create_Block(_2333_recursiveGen)))));
            RAST._IExpr _out599;
            DCOMP._IOwnership _out600;
            (this).FromOwned(r, expectedOwnership, out _out599, out _out600);
            r = _out599;
            resultingOwnership = _out600;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2345_values = _source111.dtor_values;
          DAST._IType _2346_retType = _source111.dtor_retType;
          DAST._IExpression _2347_expr = _source111.dtor_expr;
          unmatched111 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2348_paramNames;
            _2348_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2349_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out601;
            _out601 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2350_value) => {
              return (_2350_value).dtor__0;
            })), _2345_values), false);
            _2349_paramFormals = _out601;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2351_paramTypes;
            _2351_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2352_paramNamesSet;
            _2352_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi51 = new BigInteger((_2345_values).Count);
            for (BigInteger _2353_i = BigInteger.Zero; _2353_i < _hi51; _2353_i++) {
              Dafny.ISequence<Dafny.Rune> _2354_name;
              _2354_name = (((_2345_values).Select(_2353_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2355_rName;
              _2355_rName = DCOMP.__default.escapeVar(_2354_name);
              _2348_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2348_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2355_rName));
              _2351_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2351_paramTypes, _2355_rName, ((_2349_paramFormals).Select(_2353_i)).dtor_tpe);
              _2352_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2352_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2355_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi52 = new BigInteger((_2345_values).Count);
            for (BigInteger _2356_i = BigInteger.Zero; _2356_i < _hi52; _2356_i++) {
              RAST._IType _2357_typeGen;
              RAST._IType _out602;
              _out602 = (this).GenType((((_2345_values).Select(_2356_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2357_typeGen = _out602;
              RAST._IExpr _2358_valueGen;
              DCOMP._IOwnership _2359___v221;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2360_recIdents;
              RAST._IExpr _out603;
              DCOMP._IOwnership _out604;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out605;
              (this).GenExpr(((_2345_values).Select(_2356_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out603, out _out604, out _out605);
              _2358_valueGen = _out603;
              _2359___v221 = _out604;
              _2360_recIdents = _out605;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar((((_2345_values).Select(_2356_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2357_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2358_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2360_recIdents);
            }
            DCOMP._IEnvironment _2361_newEnv;
            _2361_newEnv = DCOMP.Environment.create(_2348_paramNames, _2351_paramTypes);
            RAST._IExpr _2362_recGen;
            DCOMP._IOwnership _2363_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2364_recIdents;
            RAST._IExpr _out606;
            DCOMP._IOwnership _out607;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out608;
            (this).GenExpr(_2347_expr, selfIdent, _2361_newEnv, expectedOwnership, out _out606, out _out607, out _out608);
            _2362_recGen = _out606;
            _2363_recOwned = _out607;
            _2364_recIdents = _out608;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2364_recIdents, _2352_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2362_recGen));
            RAST._IExpr _out609;
            DCOMP._IOwnership _out610;
            (this).FromOwnership(r, _2363_recOwned, expectedOwnership, out _out609, out _out610);
            r = _out609;
            resultingOwnership = _out610;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2365_name = _source111.dtor_ident;
          DAST._IType _2366_tpe = _source111.dtor_typ;
          DAST._IExpression _2367_value = _source111.dtor_value;
          DAST._IExpression _2368_iifeBody = _source111.dtor_iifeBody;
          unmatched111 = false;
          {
            RAST._IExpr _2369_valueGen;
            DCOMP._IOwnership _2370___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2371_recIdents;
            RAST._IExpr _out611;
            DCOMP._IOwnership _out612;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out613;
            (this).GenExpr(_2367_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out611, out _out612, out _out613);
            _2369_valueGen = _out611;
            _2370___v222 = _out612;
            _2371_recIdents = _out613;
            readIdents = _2371_recIdents;
            RAST._IType _2372_valueTypeGen;
            RAST._IType _out614;
            _out614 = (this).GenType(_2366_tpe, DCOMP.GenTypeContext.InFn());
            _2372_valueTypeGen = _out614;
            RAST._IExpr _2373_bodyGen;
            DCOMP._IOwnership _2374___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2375_bodyIdents;
            RAST._IExpr _out615;
            DCOMP._IOwnership _out616;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out617;
            (this).GenExpr(_2368_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out615, out _out616, out _out617);
            _2373_bodyGen = _out615;
            _2374___v223 = _out616;
            _2375_bodyIdents = _out617;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2375_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_2365_name))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar(_2365_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2372_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2369_valueGen))).Then(_2373_bodyGen));
            RAST._IExpr _out618;
            DCOMP._IOwnership _out619;
            (this).FromOwned(r, expectedOwnership, out _out618, out _out619);
            r = _out618;
            resultingOwnership = _out619;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_Apply) {
          DAST._IExpression _2376_func = _source111.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2377_args = _source111.dtor_args;
          unmatched111 = false;
          {
            RAST._IExpr _2378_funcExpr;
            DCOMP._IOwnership _2379___v224;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2380_recIdents;
            RAST._IExpr _out620;
            DCOMP._IOwnership _out621;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
            (this).GenExpr(_2376_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out620, out _out621, out _out622);
            _2378_funcExpr = _out620;
            _2379___v224 = _out621;
            _2380_recIdents = _out622;
            readIdents = _2380_recIdents;
            Dafny.ISequence<RAST._IExpr> _2381_rArgs;
            _2381_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi53 = new BigInteger((_2377_args).Count);
            for (BigInteger _2382_i = BigInteger.Zero; _2382_i < _hi53; _2382_i++) {
              RAST._IExpr _2383_argExpr;
              DCOMP._IOwnership _2384_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2385_argIdents;
              RAST._IExpr _out623;
              DCOMP._IOwnership _out624;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out625;
              (this).GenExpr((_2377_args).Select(_2382_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out623, out _out624, out _out625);
              _2383_argExpr = _out623;
              _2384_argOwned = _out624;
              _2385_argIdents = _out625;
              _2381_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2381_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2383_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2385_argIdents);
            }
            r = (_2378_funcExpr).Apply(_2381_rArgs);
            RAST._IExpr _out626;
            DCOMP._IOwnership _out627;
            (this).FromOwned(r, expectedOwnership, out _out626, out _out627);
            r = _out626;
            resultingOwnership = _out627;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_TypeTest) {
          DAST._IExpression _2386_on = _source111.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2387_dType = _source111.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2388_variant = _source111.dtor_variant;
          unmatched111 = false;
          {
            RAST._IExpr _2389_exprGen;
            DCOMP._IOwnership _2390___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2391_recIdents;
            RAST._IExpr _out628;
            DCOMP._IOwnership _out629;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out630;
            (this).GenExpr(_2386_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out628, out _out629, out _out630);
            _2389_exprGen = _out628;
            _2390___v225 = _out629;
            _2391_recIdents = _out630;
            RAST._IType _2392_dTypePath;
            RAST._IType _out631;
            _out631 = DCOMP.COMP.GenPathType(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2387_dType, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2388_variant)));
            _2392_dTypePath = _out631;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2389_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_2392_dTypePath)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out632;
            DCOMP._IOwnership _out633;
            (this).FromOwned(r, expectedOwnership, out _out632, out _out633);
            r = _out632;
            resultingOwnership = _out633;
            readIdents = _2391_recIdents;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_Is) {
          DAST._IExpression _2393_expr = _source111.dtor_expr;
          DAST._IType _2394_fromType = _source111.dtor_fromType;
          DAST._IType _2395_toType = _source111.dtor_toType;
          unmatched111 = false;
          {
            RAST._IExpr _2396_expr;
            DCOMP._IOwnership _2397_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2398_recIdents;
            RAST._IExpr _out634;
            DCOMP._IOwnership _out635;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out636;
            (this).GenExpr(_2393_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out634, out _out635, out _out636);
            _2396_expr = _out634;
            _2397_recOwned = _out635;
            _2398_recIdents = _out636;
            RAST._IType _2399_fromType;
            RAST._IType _out637;
            _out637 = (this).GenType(_2394_fromType, DCOMP.GenTypeContext.@default());
            _2399_fromType = _out637;
            RAST._IType _2400_toType;
            RAST._IType _out638;
            _out638 = (this).GenType(_2395_toType, DCOMP.GenTypeContext.@default());
            _2400_toType = _out638;
            if (((_2399_fromType).IsObject()) && ((_2400_toType).IsObject())) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is_instance_of_object"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((_2399_fromType).ObjectOrPointerUnderlying(), (_2400_toType).ObjectOrPointerUnderlying()))).Apply1(_2396_expr);
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Source and/or target types of type test is/are not Object"));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
            RAST._IExpr _out639;
            DCOMP._IOwnership _out640;
            (this).FromOwnership(r, _2397_recOwned, expectedOwnership, out _out639, out _out640);
            r = _out639;
            resultingOwnership = _out640;
            readIdents = _2398_recIdents;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_BoolBoundedPool) {
          unmatched111 = false;
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
      if (unmatched111) {
        if (_source111.is_SetBoundedPool) {
          DAST._IExpression _2401_of = _source111.dtor_of;
          unmatched111 = false;
          {
            RAST._IExpr _2402_exprGen;
            DCOMP._IOwnership _2403___v226;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2404_recIdents;
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out645;
            (this).GenExpr(_2401_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out643, out _out644, out _out645);
            _2402_exprGen = _out643;
            _2403___v226 = _out644;
            _2404_recIdents = _out645;
            r = ((_2402_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out646;
            DCOMP._IOwnership _out647;
            (this).FromOwned(r, expectedOwnership, out _out646, out _out647);
            r = _out646;
            resultingOwnership = _out647;
            readIdents = _2404_recIdents;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_SeqBoundedPool) {
          DAST._IExpression _2405_of = _source111.dtor_of;
          bool _2406_includeDuplicates = _source111.dtor_includeDuplicates;
          unmatched111 = false;
          {
            RAST._IExpr _2407_exprGen;
            DCOMP._IOwnership _2408___v227;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2409_recIdents;
            RAST._IExpr _out648;
            DCOMP._IOwnership _out649;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out650;
            (this).GenExpr(_2405_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out648, out _out649, out _out650);
            _2407_exprGen = _out648;
            _2408___v227 = _out649;
            _2409_recIdents = _out650;
            r = ((_2407_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2406_includeDuplicates)) {
              r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).AsExpr()).Apply1(r);
            }
            RAST._IExpr _out651;
            DCOMP._IOwnership _out652;
            (this).FromOwned(r, expectedOwnership, out _out651, out _out652);
            r = _out651;
            resultingOwnership = _out652;
            readIdents = _2409_recIdents;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_MapBoundedPool) {
          DAST._IExpression _2410_of = _source111.dtor_of;
          unmatched111 = false;
          {
            RAST._IExpr _2411_exprGen;
            DCOMP._IOwnership _2412___v228;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2413_recIdents;
            RAST._IExpr _out653;
            DCOMP._IOwnership _out654;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
            (this).GenExpr(_2410_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out653, out _out654, out _out655);
            _2411_exprGen = _out653;
            _2412___v228 = _out654;
            _2413_recIdents = _out655;
            r = ((((_2411_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2413_recIdents;
            RAST._IExpr _out656;
            DCOMP._IOwnership _out657;
            (this).FromOwned(r, expectedOwnership, out _out656, out _out657);
            r = _out656;
            resultingOwnership = _out657;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_IntRange) {
          DAST._IExpression _2414_lo = _source111.dtor_lo;
          DAST._IExpression _2415_hi = _source111.dtor_hi;
          bool _2416_up = _source111.dtor_up;
          unmatched111 = false;
          {
            RAST._IExpr _2417_lo;
            DCOMP._IOwnership _2418___v229;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2419_recIdentsLo;
            RAST._IExpr _out658;
            DCOMP._IOwnership _out659;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out660;
            (this).GenExpr(_2414_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out658, out _out659, out _out660);
            _2417_lo = _out658;
            _2418___v229 = _out659;
            _2419_recIdentsLo = _out660;
            RAST._IExpr _2420_hi;
            DCOMP._IOwnership _2421___v230;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2422_recIdentsHi;
            RAST._IExpr _out661;
            DCOMP._IOwnership _out662;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out663;
            (this).GenExpr(_2415_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out661, out _out662, out _out663);
            _2420_hi = _out661;
            _2421___v230 = _out662;
            _2422_recIdentsHi = _out663;
            if (_2416_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2417_lo, _2420_hi));
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2420_hi, _2417_lo));
            }
            RAST._IExpr _out664;
            DCOMP._IOwnership _out665;
            (this).FromOwned(r, expectedOwnership, out _out664, out _out665);
            r = _out664;
            resultingOwnership = _out665;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2419_recIdentsLo, _2422_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_UnboundedIntRange) {
          DAST._IExpression _2423_start = _source111.dtor_start;
          bool _2424_up = _source111.dtor_up;
          unmatched111 = false;
          {
            RAST._IExpr _2425_start;
            DCOMP._IOwnership _2426___v231;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2427_recIdentStart;
            RAST._IExpr _out666;
            DCOMP._IOwnership _out667;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out668;
            (this).GenExpr(_2423_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out666, out _out667, out _out668);
            _2425_start = _out666;
            _2426___v231 = _out667;
            _2427_recIdentStart = _out668;
            if (_2424_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).AsExpr()).Apply1(_2425_start);
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).AsExpr()).Apply1(_2425_start);
            }
            RAST._IExpr _out669;
            DCOMP._IOwnership _out670;
            (this).FromOwned(r, expectedOwnership, out _out669, out _out670);
            r = _out669;
            resultingOwnership = _out670;
            readIdents = _2427_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_MapBuilder) {
          DAST._IType _2428_keyType = _source111.dtor_keyType;
          DAST._IType _2429_valueType = _source111.dtor_valueType;
          unmatched111 = false;
          {
            RAST._IType _2430_kType;
            RAST._IType _out671;
            _out671 = (this).GenType(_2428_keyType, DCOMP.GenTypeContext.@default());
            _2430_kType = _out671;
            RAST._IType _2431_vType;
            RAST._IType _out672;
            _out672 = (this).GenType(_2429_valueType, DCOMP.GenTypeContext.@default());
            _2431_vType = _out672;
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2430_kType, _2431_vType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
      if (unmatched111) {
        if (_source111.is_SetBuilder) {
          DAST._IType _2432_elemType = _source111.dtor_elemType;
          unmatched111 = false;
          {
            RAST._IType _2433_eType;
            RAST._IType _out675;
            _out675 = (this).GenType(_2432_elemType, DCOMP.GenTypeContext.@default());
            _2433_eType = _out675;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2433_eType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out676;
            DCOMP._IOwnership _out677;
            (this).FromOwned(r, expectedOwnership, out _out676, out _out677);
            r = _out676;
            resultingOwnership = _out677;
            return ;
          }
        }
      }
      if (unmatched111) {
        DAST._IType _2434_elemType = _source111.dtor_elemType;
        DAST._IExpression _2435_collection = _source111.dtor_collection;
        bool _2436_is__forall = _source111.dtor_is__forall;
        DAST._IExpression _2437_lambda = _source111.dtor_lambda;
        unmatched111 = false;
        {
          RAST._IType _2438_tpe;
          RAST._IType _out678;
          _out678 = (this).GenType(_2434_elemType, DCOMP.GenTypeContext.@default());
          _2438_tpe = _out678;
          RAST._IExpr _2439_collectionGen;
          DCOMP._IOwnership _2440___v232;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2441_recIdents;
          RAST._IExpr _out679;
          DCOMP._IOwnership _out680;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out681;
          (this).GenExpr(_2435_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out679, out _out680, out _out681);
          _2439_collectionGen = _out679;
          _2440___v232 = _out680;
          _2441_recIdents = _out681;
          Dafny.ISequence<DAST._IAttribute> _2442_extraAttributes;
          _2442_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2435_collection).is_IntRange) || ((_2435_collection).is_UnboundedIntRange)) || ((_2435_collection).is_SeqBoundedPool)) {
            _2442_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2437_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2443_formals;
            _2443_formals = (_2437_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2444_newFormals;
            _2444_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi54 = new BigInteger((_2443_formals).Count);
            for (BigInteger _2445_i = BigInteger.Zero; _2445_i < _hi54; _2445_i++) {
              var _pat_let_tv200 = _2442_extraAttributes;
              var _pat_let_tv201 = _2443_formals;
              _2444_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2444_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2443_formals).Select(_2445_i), _pat_let50_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let50_0, _2446_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv200, ((_pat_let_tv201).Select(_2445_i)).dtor_attributes), _pat_let51_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let51_0, _2447_dt__update_hattributes_h0 => DAST.Formal.create((_2446_dt__update__tmp_h0).dtor_name, (_2446_dt__update__tmp_h0).dtor_typ, _2447_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv202 = _2444_newFormals;
            DAST._IExpression _2448_newLambda;
            _2448_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2437_lambda, _pat_let52_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let52_0, _2449_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv202, _pat_let53_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let53_0, _2450_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2450_dt__update_hparams_h0, (_2449_dt__update__tmp_h1).dtor_retType, (_2449_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2451_lambdaGen;
            DCOMP._IOwnership _2452___v233;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2453_recLambdaIdents;
            RAST._IExpr _out682;
            DCOMP._IOwnership _out683;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out684;
            (this).GenExpr(_2448_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out682, out _out683, out _out684);
            _2451_lambdaGen = _out682;
            _2452___v233 = _out683;
            _2453_recLambdaIdents = _out684;
            Dafny.ISequence<Dafny.Rune> _2454_fn;
            _2454_fn = ((_2436_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2439_collectionGen).Sel(_2454_fn)).Apply1(((_2451_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2441_recIdents, _2453_recLambdaIdents);
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
      Dafny.ISequence<RAST._IModDecl> _2455_externUseDecls;
      _2455_externUseDecls = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi55 = new BigInteger((externalFiles).Count);
      for (BigInteger _2456_i = BigInteger.Zero; _2456_i < _hi55; _2456_i++) {
        Dafny.ISequence<Dafny.Rune> _2457_externalFile;
        _2457_externalFile = (externalFiles).Select(_2456_i);
        Dafny.ISequence<Dafny.Rune> _2458_externalMod;
        _2458_externalMod = _2457_externalFile;
        if (((new BigInteger((_2457_externalFile).Count)) > (new BigInteger(3))) && (((_2457_externalFile).Drop((new BigInteger((_2457_externalFile).Count)) - (new BigInteger(3)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".rs")))) {
          _2458_externalMod = (_2457_externalFile).Subsequence(BigInteger.Zero, (new BigInteger((_2457_externalFile).Count)) - (new BigInteger(3)));
        } else {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unrecognized external file "), _2457_externalFile), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". External file must be *.rs files")));
        }
        RAST._IMod _2459_externMod;
        _2459_externMod = RAST.Mod.create_ExternMod(_2458_externalMod);
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (_2459_externMod)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        _2455_externUseDecls = Dafny.Sequence<RAST._IModDecl>.Concat(_2455_externUseDecls, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), ((RAST.__default.crate).MSel(_2458_externalMod)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))));
      }
      if (!(_2455_externUseDecls).Equals(Dafny.Sequence<RAST._IModDecl>.FromElements())) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (RAST.Mod.create_Mod(DCOMP.COMP.DAFNY__EXTERN__MODULE, _2455_externUseDecls))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
      }
      DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _2460_allModules;
      _2460_allModules = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Empty();
      BigInteger _hi56 = new BigInteger((p).Count);
      for (BigInteger _2461_i = BigInteger.Zero; _2461_i < _hi56; _2461_i++) {
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _2462_m;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out687;
        _out687 = (this).GenModule((p).Select(_2461_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2462_m = _out687;
        _2460_allModules = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(_2460_allModules, _2462_m);
      }
      BigInteger _hi57 = new BigInteger(((_2460_allModules).dtor_keys).Count);
      for (BigInteger _2463_i = BigInteger.Zero; _2463_i < _hi57; _2463_i++) {
        if (!((_2460_allModules).dtor_values).Contains(((_2460_allModules).dtor_keys).Select(_2463_i))) {
          goto continue_0;
        }
        RAST._IMod _2464_m;
        _2464_m = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Select((_2460_allModules).dtor_values,((_2460_allModules).dtor_keys).Select(_2463_i))).ToRust();
        BigInteger _hi58 = new BigInteger((this.optimizations).Count);
        for (BigInteger _2465_j = BigInteger.Zero; _2465_j < _hi58; _2465_j++) {
          _2464_m = Dafny.Helpers.Id<Func<RAST._IMod, RAST._IMod>>((this.optimizations).Select(_2465_j))(_2464_m);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (_2464_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      continue_0: ;
      }
    after_0: ;
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2466_i;
      _2466_i = BigInteger.Zero;
      while ((_2466_i) < (new BigInteger((fullName).Count))) {
        if ((_2466_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2466_i)));
        _2466_i = (_2466_i) + (BigInteger.One);
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