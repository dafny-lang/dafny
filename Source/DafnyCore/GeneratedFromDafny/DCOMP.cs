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
    public Dafny.ISet<Dafny.ISequence<Dafny.Rune>> GatherTypeParamNames(Dafny.ISet<Dafny.ISequence<Dafny.Rune>> types, RAST._IType typ)
    {
      return (typ).Fold<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>(types, ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>, RAST._IType, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)((_1333_types, _1334_currentType) => {
        return (((_1334_currentType).is_TIdentifier) ? (Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1333_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_1334_currentType).dtor_name))) : (_1333_types));
      })));
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1335_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1336_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1337_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1338_whereConstraints;
      Dafny.ISequence<DAST._IType> _out26;
      Dafny.ISequence<RAST._IType> _out27;
      Dafny.ISequence<RAST._ITypeParamDecl> _out28;
      Dafny.ISequence<Dafny.Rune> _out29;
      (this).GenTypeParameters((c).dtor_typeParams, out _out26, out _out27, out _out28, out _out29);
      _1335_typeParamsSeq = _out26;
      _1336_rTypeParams = _out27;
      _1337_rTypeParamsDecls = _out28;
      _1338_whereConstraints = _out29;
      Dafny.ISequence<Dafny.Rune> _1339_constrainedTypeParams;
      _1339_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1337_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1340_fields;
      _1340_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1341_fieldInits;
      _1341_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1342_usedTypeParams;
      _1342_usedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi8 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1343_fieldI = BigInteger.Zero; _1343_fieldI < _hi8; _1343_fieldI++) {
        DAST._IField _1344_field;
        _1344_field = ((c).dtor_fields).Select(_1343_fieldI);
        RAST._IType _1345_fieldType;
        RAST._IType _out30;
        _out30 = (this).GenType(((_1344_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1345_fieldType = _out30;
        _1342_usedTypeParams = (this).GatherTypeParamNames(_1342_usedTypeParams, _1345_fieldType);
        Dafny.ISequence<Dafny.Rune> _1346_fieldRustName;
        _1346_fieldRustName = DCOMP.__default.escapeVar(((_1344_field).dtor_formal).dtor_name);
        _1340_fields = Dafny.Sequence<RAST._IField>.Concat(_1340_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1346_fieldRustName, _1345_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source69 = (_1344_field).dtor_defaultValue;
        bool unmatched69 = true;
        if (unmatched69) {
          if (_source69.is_Some) {
            DAST._IExpression _1347_e = _source69.dtor_value;
            unmatched69 = false;
            {
              RAST._IExpr _1348_expr;
              DCOMP._IOwnership _1349___v51;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1350___v52;
              RAST._IExpr _out31;
              DCOMP._IOwnership _out32;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out33;
              (this).GenExpr(_1347_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out31, out _out32, out _out33);
              _1348_expr = _out31;
              _1349___v51 = _out32;
              _1350___v52 = _out33;
              _1341_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1341_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1346_fieldRustName, _1348_expr)));
            }
          }
        }
        if (unmatched69) {
          unmatched69 = false;
          {
            RAST._IExpr _1351_default;
            _1351_default = RAST.__default.std__Default__default;
            if ((_1345_fieldType).IsObjectOrPointer()) {
              _1351_default = (_1345_fieldType).ToNullExpr();
            }
            _1341_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1341_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1346_fieldRustName, _1351_default)));
          }
        }
      }
      BigInteger _hi9 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1352_typeParamI = BigInteger.Zero; _1352_typeParamI < _hi9; _1352_typeParamI++) {
        DAST._IType _1353_typeArg;
        RAST._ITypeParamDecl _1354_typeParam;
        DAST._IType _out34;
        RAST._ITypeParamDecl _out35;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1352_typeParamI), out _out34, out _out35);
        _1353_typeArg = _out34;
        _1354_typeParam = _out35;
        RAST._IType _1355_rTypeArg;
        RAST._IType _out36;
        _out36 = (this).GenType(_1353_typeArg, DCOMP.GenTypeContext.@default());
        _1355_rTypeArg = _out36;
        if ((_1342_usedTypeParams).Contains((_1354_typeParam).dtor_name)) {
          goto continue_0;
        }
        _1340_fields = Dafny.Sequence<RAST._IField>.Concat(_1340_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1352_typeParamI)), RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1355_rTypeArg))))));
        _1341_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1341_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1352_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      continue_0: ;
      }
    after_0: ;
      DCOMP._IExternAttribute _1356_extern;
      _1356_extern = DCOMP.__default.ExtractExtern((c).dtor_attributes, (c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _1357_className = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((_1356_extern).is_SimpleExtern) {
        _1357_className = (_1356_extern).dtor_overrideName;
      } else {
        _1357_className = DCOMP.__default.escapeName((c).dtor_name);
        if ((_1356_extern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multi-argument externs not supported for classes yet"));
        }
      }
      RAST._IStruct _1358_struct;
      _1358_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1357_className, _1337_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1340_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_1356_extern).is_NoExtern) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1358_struct)));
      }
      Dafny.ISequence<RAST._IImplMember> _1359_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1360_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out37;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out38;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1335_typeParamsSeq, out _out37, out _out38);
      _1359_implBody = _out37;
      _1360_traitBodies = _out38;
      if (((_1356_extern).is_NoExtern) && (!(_1357_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default")))) {
        _1359_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.__default.SelfOwned)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel((this).allocate)).AsExpr()).ApplyType1(RAST.__default.SelfOwned)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1359_implBody);
      }
      RAST._IType _1361_selfTypeForImpl = RAST.Type.Default();
      if (((_1356_extern).is_NoExtern) || ((_1356_extern).is_UnsupportedExtern)) {
        _1361_selfTypeForImpl = RAST.Type.create_TIdentifier(_1357_className);
      } else if ((_1356_extern).is_AdvancedExtern) {
        _1361_selfTypeForImpl = (((RAST.__default.crate).MSel((_1356_extern).dtor_enclosingModule)).MSel((_1356_extern).dtor_overrideName)).AsType();
      } else if ((_1356_extern).is_SimpleExtern) {
        _1361_selfTypeForImpl = RAST.Type.create_TIdentifier((_1356_extern).dtor_overrideName);
      }
      if ((new BigInteger((_1359_implBody).Count)).Sign == 1) {
        RAST._IImpl _1362_i;
        _1362_i = RAST.Impl.create_Impl(_1337_rTypeParamsDecls, RAST.Type.create_TypeApp(_1361_selfTypeForImpl, _1336_rTypeParams), _1338_whereConstraints, _1359_implBody);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1362_i)));
      }
      RAST._IType _1363_genSelfPath;
      RAST._IType _out39;
      _out39 = DCOMP.COMP.GenPathType(path);
      _1363_genSelfPath = _out39;
      if (!(_1357_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1337_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(RAST.__default.AnyTrait))), RAST.Type.create_TypeApp(_1363_genSelfPath, _1336_rTypeParams), _1338_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(RAST.__default.AnyTrait)))))))));
      }
      Dafny.ISequence<DAST._IType> _1364_superClasses;
      _1364_superClasses = (((_1357_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) ? (Dafny.Sequence<DAST._IType>.FromElements()) : ((c).dtor_superClasses));
      BigInteger _hi10 = new BigInteger((_1364_superClasses).Count);
      for (BigInteger _1365_i = BigInteger.Zero; _1365_i < _hi10; _1365_i++) {
        DAST._IType _1366_superClass;
        _1366_superClass = (_1364_superClasses).Select(_1365_i);
        DAST._IType _source70 = _1366_superClass;
        bool unmatched70 = true;
        if (unmatched70) {
          if (_source70.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source70.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1367_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1368_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1369_properMethods = resolved0.dtor_properMethods;
              unmatched70 = false;
              {
                RAST._IType _1370_pathStr;
                RAST._IType _out40;
                _out40 = DCOMP.COMP.GenPathType(_1367_traitPath);
                _1370_pathStr = _out40;
                Dafny.ISequence<RAST._IType> _1371_typeArgs;
                Dafny.ISequence<RAST._IType> _out41;
                _out41 = (this).GenTypeArgs(_1368_typeArgs, DCOMP.GenTypeContext.@default());
                _1371_typeArgs = _out41;
                Dafny.ISequence<RAST._IImplMember> _1372_body;
                _1372_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1360_traitBodies).Contains(_1367_traitPath)) {
                  _1372_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1360_traitBodies,_1367_traitPath);
                }
                RAST._IType _1373_traitType;
                _1373_traitType = RAST.Type.create_TypeApp(_1370_pathStr, _1371_typeArgs);
                if (!((_1356_extern).is_NoExtern)) {
                  if (((new BigInteger((_1372_body).Count)).Sign == 0) && ((new BigInteger((_1369_properMethods).Count)).Sign != 0)) {
                    goto continue_1;
                  }
                  if ((new BigInteger((_1372_body).Count)) != (new BigInteger((_1369_properMethods).Count))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: In the class "), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(path, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1374_s) => {
  return ((_1374_s));
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", some proper methods of ")), (_1373_traitType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" are marked {:extern} and some are not.")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" For the Rust compiler, please make all methods (")), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_1369_properMethods, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1375_s) => {
  return (_1375_s);
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")  bodiless and mark as {:extern} and implement them in a Rust file, ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("or mark none of them as {:extern} and implement them in Dafny. ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.")));
                  }
                }
                RAST._IModDecl _1376_x;
                _1376_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1337_rTypeParamsDecls, _1373_traitType, RAST.Type.create_TypeApp(_1363_genSelfPath, _1336_rTypeParams), _1338_whereConstraints, _1372_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1376_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1337_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1373_traitType))), RAST.Type.create_TypeApp(_1363_genSelfPath, _1336_rTypeParams), _1338_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1373_traitType)))))))));
              }
            }
          }
        }
        if (unmatched70) {
          unmatched70 = false;
        }
      continue_1: ;
      }
    after_1: ;
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1377_typeParamsSeq;
      _1377_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1378_typeParamDecls;
      _1378_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1379_typeParams;
      _1379_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi11 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1380_tpI = BigInteger.Zero; _1380_tpI < _hi11; _1380_tpI++) {
          DAST._ITypeArgDecl _1381_tp;
          _1381_tp = ((t).dtor_typeParams).Select(_1380_tpI);
          DAST._IType _1382_typeArg;
          RAST._ITypeParamDecl _1383_typeParamDecl;
          DAST._IType _out42;
          RAST._ITypeParamDecl _out43;
          (this).GenTypeParam(_1381_tp, out _out42, out _out43);
          _1382_typeArg = _out42;
          _1383_typeParamDecl = _out43;
          _1377_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1377_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1382_typeArg));
          _1378_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1378_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1383_typeParamDecl));
          RAST._IType _1384_typeParam;
          RAST._IType _out44;
          _out44 = (this).GenType(_1382_typeArg, DCOMP.GenTypeContext.@default());
          _1384_typeParam = _out44;
          _1379_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1379_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1384_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1385_fullPath;
      _1385_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1386_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1387___v56;
      Dafny.ISequence<RAST._IImplMember> _out45;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out46;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1385_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1377_typeParamsSeq, out _out45, out _out46);
      _1386_implBody = _out45;
      _1387___v56 = _out46;
      Dafny.ISequence<RAST._IType> _1388_parents;
      _1388_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi12 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1389_i = BigInteger.Zero; _1389_i < _hi12; _1389_i++) {
        RAST._IType _1390_tpe;
        RAST._IType _out47;
        _out47 = (this).GenType(((t).dtor_parents).Select(_1389_i), DCOMP.GenTypeContext.ForTraitParents());
        _1390_tpe = _out47;
        _1388_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1388_parents, Dafny.Sequence<RAST._IType>.FromElements(_1390_tpe)), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply1(RAST.Type.create_DynType(_1390_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1378_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1379_typeParams), _1388_parents, _1386_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1391_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1392_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1393_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1394_whereConstraints;
      Dafny.ISequence<DAST._IType> _out48;
      Dafny.ISequence<RAST._IType> _out49;
      Dafny.ISequence<RAST._ITypeParamDecl> _out50;
      Dafny.ISequence<Dafny.Rune> _out51;
      (this).GenTypeParameters((c).dtor_typeParams, out _out48, out _out49, out _out50, out _out51);
      _1391_typeParamsSeq = _out48;
      _1392_rTypeParams = _out49;
      _1393_rTypeParamsDecls = _out50;
      _1394_whereConstraints = _out51;
      Dafny.ISequence<Dafny.Rune> _1395_constrainedTypeParams;
      _1395_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1393_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1396_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source71 = DCOMP.COMP.NewtypeRangeToRustType((c).dtor_range);
      bool unmatched71 = true;
      if (unmatched71) {
        if (_source71.is_Some) {
          RAST._IType _1397_v = _source71.dtor_value;
          unmatched71 = false;
          _1396_underlyingType = _1397_v;
        }
      }
      if (unmatched71) {
        unmatched71 = false;
        RAST._IType _out52;
        _out52 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1396_underlyingType = _out52;
      }
      DAST._IType _1398_resultingType;
      _1398_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1399_newtypeName;
      _1399_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1399_newtypeName, _1393_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1396_underlyingType))))));
      RAST._IExpr _1400_fnBody;
      _1400_fnBody = RAST.Expr.create_Identifier(_1399_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source72 = (c).dtor_witnessExpr;
      bool unmatched72 = true;
      if (unmatched72) {
        if (_source72.is_Some) {
          DAST._IExpression _1401_e = _source72.dtor_value;
          unmatched72 = false;
          {
            DAST._IExpression _1402_e;
            _1402_e = ((object.Equals((c).dtor_base, _1398_resultingType)) ? (_1401_e) : (DAST.Expression.create_Convert(_1401_e, (c).dtor_base, _1398_resultingType)));
            RAST._IExpr _1403_eStr;
            DCOMP._IOwnership _1404___v57;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1405___v58;
            RAST._IExpr _out53;
            DCOMP._IOwnership _out54;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out55;
            (this).GenExpr(_1402_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out53, out _out54, out _out55);
            _1403_eStr = _out53;
            _1404___v57 = _out54;
            _1405___v58 = _out55;
            _1400_fnBody = (_1400_fnBody).Apply1(_1403_eStr);
          }
        }
      }
      if (unmatched72) {
        unmatched72 = false;
        {
          _1400_fnBody = (_1400_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1406_body;
      _1406_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1400_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source73 = (c).dtor_constraint;
      bool unmatched73 = true;
      if (unmatched73) {
        if (_source73.is_None) {
          unmatched73 = false;
        }
      }
      if (unmatched73) {
        DAST._INewtypeConstraint value8 = _source73.dtor_value;
        DAST._IFormal _1407_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1408_constraintStmts = value8.dtor_constraintStmts;
        unmatched73 = false;
        RAST._IExpr _1409_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1410___v59;
        DCOMP._IEnvironment _1411_newEnv;
        RAST._IExpr _out56;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out57;
        DCOMP._IEnvironment _out58;
        (this).GenStmts(_1408_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out56, out _out57, out _out58);
        _1409_rStmts = _out56;
        _1410___v59 = _out57;
        _1411_newEnv = _out58;
        Dafny.ISequence<RAST._IFormal> _1412_rFormals;
        Dafny.ISequence<RAST._IFormal> _out59;
        _out59 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1407_formal), false);
        _1412_rFormals = _out59;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1393_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1399_newtypeName), _1392_rTypeParams), _1394_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1412_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1409_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1393_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1399_newtypeName), _1392_rTypeParams), _1394_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1406_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1393_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1399_newtypeName), _1392_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1393_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1399_newtypeName), _1392_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1396_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(((RAST.Path.create_Self()).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))).AsType())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1413_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1414_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1415_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1416_whereConstraints;
      Dafny.ISequence<DAST._IType> _out60;
      Dafny.ISequence<RAST._IType> _out61;
      Dafny.ISequence<RAST._ITypeParamDecl> _out62;
      Dafny.ISequence<Dafny.Rune> _out63;
      (this).GenTypeParameters((c).dtor_typeParams, out _out60, out _out61, out _out62, out _out63);
      _1413_typeParamsSeq = _out60;
      _1414_rTypeParams = _out61;
      _1415_rTypeParamsDecls = _out62;
      _1416_whereConstraints = _out63;
      Dafny.ISequence<Dafny.Rune> _1417_synonymTypeName;
      _1417_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1418_resultingType;
      RAST._IType _out64;
      _out64 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1418_resultingType = _out64;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1417_synonymTypeName, _1415_rTypeParamsDecls, _1418_resultingType)));
      Dafny.ISequence<RAST._ITypeParamDecl> _1419_defaultConstrainedTypeParams;
      _1419_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1415_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Std.Wrappers._IOption<DAST._IExpression> _source74 = (c).dtor_witnessExpr;
      bool unmatched74 = true;
      if (unmatched74) {
        if (_source74.is_Some) {
          DAST._IExpression _1420_e = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IExpr _1421_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1422___v60;
            DCOMP._IEnvironment _1423_newEnv;
            RAST._IExpr _out65;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out66;
            DCOMP._IEnvironment _out67;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out65, out _out66, out _out67);
            _1421_rStmts = _out65;
            _1422___v60 = _out66;
            _1423_newEnv = _out67;
            RAST._IExpr _1424_rExpr;
            DCOMP._IOwnership _1425___v61;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1426___v62;
            RAST._IExpr _out68;
            DCOMP._IOwnership _out69;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out70;
            (this).GenExpr(_1420_e, DCOMP.SelfInfo.create_NoSelf(), _1423_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out68, out _out69, out _out70);
            _1424_rExpr = _out68;
            _1425___v61 = _out69;
            _1426___v62 = _out70;
            Dafny.ISequence<Dafny.Rune> _1427_constantName;
            _1427_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1427_constantName, _1419_defaultConstrainedTypeParams, Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1418_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1421_rStmts).Then(_1424_rExpr)))))));
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
          Dafny.ISequence<DAST._IType> _1428_ts = _source75.dtor_Tuple_a0;
          unmatched75 = false;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1429_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1429_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1430_t = (DAST._IType)_forall_var_5;
            return !((_1429_ts).Contains(_1430_t)) || ((this).TypeIsEq(_1430_t));
          }))))(_1428_ts);
        }
      }
      if (unmatched75) {
        if (_source75.is_Array) {
          DAST._IType _1431_t = _source75.dtor_element;
          unmatched75 = false;
          return (this).TypeIsEq(_1431_t);
        }
      }
      if (unmatched75) {
        if (_source75.is_Seq) {
          DAST._IType _1432_t = _source75.dtor_element;
          unmatched75 = false;
          return (this).TypeIsEq(_1432_t);
        }
      }
      if (unmatched75) {
        if (_source75.is_Set) {
          DAST._IType _1433_t = _source75.dtor_element;
          unmatched75 = false;
          return (this).TypeIsEq(_1433_t);
        }
      }
      if (unmatched75) {
        if (_source75.is_Multiset) {
          DAST._IType _1434_t = _source75.dtor_element;
          unmatched75 = false;
          return (this).TypeIsEq(_1434_t);
        }
      }
      if (unmatched75) {
        if (_source75.is_Map) {
          DAST._IType _1435_k = _source75.dtor_key;
          DAST._IType _1436_v = _source75.dtor_value;
          unmatched75 = false;
          return ((this).TypeIsEq(_1435_k)) && ((this).TypeIsEq(_1436_v));
        }
      }
      if (unmatched75) {
        if (_source75.is_SetBuilder) {
          DAST._IType _1437_t = _source75.dtor_element;
          unmatched75 = false;
          return (this).TypeIsEq(_1437_t);
        }
      }
      if (unmatched75) {
        if (_source75.is_MapBuilder) {
          DAST._IType _1438_k = _source75.dtor_key;
          DAST._IType _1439_v = _source75.dtor_value;
          unmatched75 = false;
          return ((this).TypeIsEq(_1438_k)) && ((this).TypeIsEq(_1439_v));
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
          Dafny.ISequence<Dafny.Rune> _1440_i = _source75.dtor_TypeArg_a0;
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
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1441_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1441_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1442_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1442_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1443_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1441_c).dtor_ctors).Contains(_1442_ctor)) && (((_1442_ctor).dtor_args).Contains(_1443_arg))) || ((this).TypeIsEq(((_1443_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1444_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1445_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1446_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1447_whereConstraints;
      Dafny.ISequence<DAST._IType> _out71;
      Dafny.ISequence<RAST._IType> _out72;
      Dafny.ISequence<RAST._ITypeParamDecl> _out73;
      Dafny.ISequence<Dafny.Rune> _out74;
      (this).GenTypeParameters((c).dtor_typeParams, out _out71, out _out72, out _out73, out _out74);
      _1444_typeParamsSeq = _out71;
      _1445_rTypeParams = _out72;
      _1446_rTypeParamsDecls = _out73;
      _1447_whereConstraints = _out74;
      Dafny.ISequence<Dafny.Rune> _1448_datatypeName;
      _1448_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1449_ctors;
      _1449_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _1450_variances;
      _1450_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_1451_typeParamDecl) => {
        return (_1451_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1452_usedTypeParams;
      _1452_usedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1453_i = BigInteger.Zero; _1453_i < _hi13; _1453_i++) {
        DAST._IDatatypeCtor _1454_ctor;
        _1454_ctor = ((c).dtor_ctors).Select(_1453_i);
        Dafny.ISequence<RAST._IField> _1455_ctorArgs;
        _1455_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1456_isNumeric;
        _1456_isNumeric = false;
        BigInteger _hi14 = new BigInteger(((_1454_ctor).dtor_args).Count);
        for (BigInteger _1457_j = BigInteger.Zero; _1457_j < _hi14; _1457_j++) {
          DAST._IDatatypeDtor _1458_dtor;
          _1458_dtor = ((_1454_ctor).dtor_args).Select(_1457_j);
          RAST._IType _1459_formalType;
          RAST._IType _out75;
          _out75 = (this).GenType(((_1458_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1459_formalType = _out75;
          _1452_usedTypeParams = (this).GatherTypeParamNames(_1452_usedTypeParams, _1459_formalType);
          Dafny.ISequence<Dafny.Rune> _1460_formalName;
          _1460_formalName = DCOMP.__default.escapeVar(((_1458_dtor).dtor_formal).dtor_name);
          if (((_1457_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1460_formalName))) {
            _1456_isNumeric = true;
          }
          if ((((_1457_j).Sign != 0) && (_1456_isNumeric)) && (!(Std.Strings.__default.OfNat(_1457_j)).Equals(_1460_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1460_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1457_j)));
            _1456_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1455_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1455_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1460_formalName, RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1459_formalType))))));
          } else {
            _1455_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1455_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1460_formalName, _1459_formalType))));
          }
        }
        RAST._IFields _1461_namedFields;
        _1461_namedFields = RAST.Fields.create_NamedFields(_1455_ctorArgs);
        if (_1456_isNumeric) {
          _1461_namedFields = (_1461_namedFields).ToNamelessFields();
        }
        _1449_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1449_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1454_ctor).dtor_name), _1461_namedFields)));
      }
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1462_unusedTypeParams;
      _1462_unusedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Helpers.Id<Func<Dafny.ISequence<RAST._ITypeParamDecl>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_1463_rTypeParamsDecls) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
        var _coll9 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
        foreach (RAST._ITypeParamDecl _compr_10 in (_1463_rTypeParamsDecls).CloneAsArray()) {
          RAST._ITypeParamDecl _1464_tp = (RAST._ITypeParamDecl)_compr_10;
          if ((_1463_rTypeParamsDecls).Contains(_1464_tp)) {
            _coll9.Add((_1464_tp).dtor_name);
          }
        }
        return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll9);
      }))())(_1446_rTypeParamsDecls), _1452_usedTypeParams);
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1465_selfPath;
      _1465_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1466_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1467_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out76;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out77;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1465_selfPath, _1444_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1450_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1444_typeParamsSeq, out _out76, out _out77);
      _1466_implBodyRaw = _out76;
      _1467_traitBodies = _out77;
      Dafny.ISequence<RAST._IImplMember> _1468_implBody;
      _1468_implBody = _1466_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1469_emittedFields;
      _1469_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi15 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1470_i = BigInteger.Zero; _1470_i < _hi15; _1470_i++) {
        DAST._IDatatypeCtor _1471_ctor;
        _1471_ctor = ((c).dtor_ctors).Select(_1470_i);
        BigInteger _hi16 = new BigInteger(((_1471_ctor).dtor_args).Count);
        for (BigInteger _1472_j = BigInteger.Zero; _1472_j < _hi16; _1472_j++) {
          DAST._IDatatypeDtor _1473_dtor;
          _1473_dtor = ((_1471_ctor).dtor_args).Select(_1472_j);
          Dafny.ISequence<Dafny.Rune> _1474_callName;
          _1474_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1473_dtor).dtor_callName, DCOMP.__default.escapeVar(((_1473_dtor).dtor_formal).dtor_name));
          if (!((_1469_emittedFields).Contains(_1474_callName))) {
            _1469_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1469_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1474_callName));
            RAST._IType _1475_formalType;
            RAST._IType _out78;
            _out78 = (this).GenType(((_1473_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1475_formalType = _out78;
            Dafny.ISequence<RAST._IMatchCase> _1476_cases;
            _1476_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi17 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1477_k = BigInteger.Zero; _1477_k < _hi17; _1477_k++) {
              DAST._IDatatypeCtor _1478_ctor2;
              _1478_ctor2 = ((c).dtor_ctors).Select(_1477_k);
              Dafny.ISequence<Dafny.Rune> _1479_pattern;
              _1479_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1448_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1478_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1480_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1481_hasMatchingField;
              _1481_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1482_patternInner;
              _1482_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1483_isNumeric;
              _1483_isNumeric = false;
              BigInteger _hi18 = new BigInteger(((_1478_ctor2).dtor_args).Count);
              for (BigInteger _1484_l = BigInteger.Zero; _1484_l < _hi18; _1484_l++) {
                DAST._IDatatypeDtor _1485_dtor2;
                _1485_dtor2 = ((_1478_ctor2).dtor_args).Select(_1484_l);
                Dafny.ISequence<Dafny.Rune> _1486_patternName;
                _1486_patternName = DCOMP.__default.escapeVar(((_1485_dtor2).dtor_formal).dtor_name);
                if (((_1484_l).Sign == 0) && ((_1486_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1483_isNumeric = true;
                }
                if (_1483_isNumeric) {
                  _1486_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1485_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1484_l)));
                }
                if (object.Equals(((_1473_dtor).dtor_formal).dtor_name, ((_1485_dtor2).dtor_formal).dtor_name)) {
                  _1481_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1486_patternName);
                }
                _1482_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1482_patternInner, _1486_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1483_isNumeric) {
                _1479_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1479_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1482_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1479_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1479_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1482_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1481_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1480_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1481_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1480_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1481_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1480_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _1487_ctorMatch;
              _1487_ctorMatch = RAST.MatchCase.create(_1479_pattern, RAST.Expr.create_RawExpr(_1480_rhs));
              _1476_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1476_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1487_ctorMatch));
            }
            if (((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) && ((new BigInteger((_1462_unusedTypeParams).Count)).Sign == 1)) {
              _1476_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1476_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1448_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _1488_methodBody;
            _1488_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1476_cases);
            _1468_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1468_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1474_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1475_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1488_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1489_coerceTypes;
      _1489_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1490_rCoerceTypeParams;
      _1490_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1491_coerceArguments;
      _1491_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1492_coerceMap;
      _1492_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1493_rCoerceMap;
      _1493_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1494_coerceMapToArg;
      _1494_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1495_types;
        _1495_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi19 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1496_typeI = BigInteger.Zero; _1496_typeI < _hi19; _1496_typeI++) {
          DAST._ITypeArgDecl _1497_typeParam;
          _1497_typeParam = ((c).dtor_typeParams).Select(_1496_typeI);
          DAST._IType _1498_typeArg;
          RAST._ITypeParamDecl _1499_rTypeParamDecl;
          DAST._IType _out79;
          RAST._ITypeParamDecl _out80;
          (this).GenTypeParam(_1497_typeParam, out _out79, out _out80);
          _1498_typeArg = _out79;
          _1499_rTypeParamDecl = _out80;
          RAST._IType _1500_rTypeArg;
          RAST._IType _out81;
          _out81 = (this).GenType(_1498_typeArg, DCOMP.GenTypeContext.@default());
          _1500_rTypeArg = _out81;
          _1495_types = Dafny.Sequence<RAST._IType>.Concat(_1495_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1500_rTypeArg))));
          if (((_1496_typeI) < (new BigInteger((_1450_variances).Count))) && (((_1450_variances).Select(_1496_typeI)).is_Nonvariant)) {
            _1489_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1489_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1500_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1501_coerceTypeParam;
          _1501_coerceTypeParam = Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_1497_typeParam, _pat_let20_0 => Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_pat_let20_0, _1502_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1496_typeI)), _pat_let21_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(_pat_let21_0, _1503_dt__update_hname_h0 => DAST.TypeArgDecl.create(_1503_dt__update_hname_h0, (_1502_dt__update__tmp_h0).dtor_bounds, (_1502_dt__update__tmp_h0).dtor_variance)))));
          DAST._IType _1504_coerceTypeArg;
          RAST._ITypeParamDecl _1505_rCoerceTypeParamDecl;
          DAST._IType _out82;
          RAST._ITypeParamDecl _out83;
          (this).GenTypeParam(_1501_coerceTypeParam, out _out82, out _out83);
          _1504_coerceTypeArg = _out82;
          _1505_rCoerceTypeParamDecl = _out83;
          _1492_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1492_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1498_typeArg, _1504_coerceTypeArg)));
          RAST._IType _1506_rCoerceType;
          RAST._IType _out84;
          _out84 = (this).GenType(_1504_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1506_rCoerceType = _out84;
          _1493_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1493_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1500_rTypeArg, _1506_rCoerceType)));
          _1489_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1489_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1506_rCoerceType));
          _1490_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1490_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1505_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1507_coerceFormal;
          _1507_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1496_typeI));
          _1494_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1494_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1500_rTypeArg, _1506_rCoerceType), (RAST.Expr.create_Identifier(_1507_coerceFormal)).Clone())));
          _1491_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1491_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1507_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1500_rTypeArg), _1506_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        if ((new BigInteger((_1462_unusedTypeParams).Count)).Sign == 1) {
          _1449_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1449_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1508_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1508_tpe);
})), _1495_types)))));
        }
      }
      bool _1509_cIsEq;
      _1509_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1509_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1448_datatypeName, _1446_rTypeParamsDecls, _1449_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1446_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1448_datatypeName), _1445_rTypeParams), _1447_whereConstraints, _1468_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1510_printImplBodyCases;
      _1510_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1511_hashImplBodyCases;
      _1511_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1512_coerceImplBodyCases;
      _1512_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi20 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1513_i = BigInteger.Zero; _1513_i < _hi20; _1513_i++) {
        DAST._IDatatypeCtor _1514_ctor;
        _1514_ctor = ((c).dtor_ctors).Select(_1513_i);
        Dafny.ISequence<Dafny.Rune> _1515_ctorMatch;
        _1515_ctorMatch = DCOMP.__default.escapeName((_1514_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1516_modulePrefix;
        _1516_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1517_ctorName;
        _1517_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1516_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1514_ctor).dtor_name));
        if (((new BigInteger((_1517_ctorName).Count)) >= (new BigInteger(13))) && (((_1517_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1517_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1518_printRhs;
        _1518_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1517_ctorName), (((_1514_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1519_hashRhs;
        _1519_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1520_coerceRhsArgs;
        _1520_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1521_isNumeric;
        _1521_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1522_ctorMatchInner;
        _1522_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi21 = new BigInteger(((_1514_ctor).dtor_args).Count);
        for (BigInteger _1523_j = BigInteger.Zero; _1523_j < _hi21; _1523_j++) {
          DAST._IDatatypeDtor _1524_dtor;
          _1524_dtor = ((_1514_ctor).dtor_args).Select(_1523_j);
          Dafny.ISequence<Dafny.Rune> _1525_patternName;
          _1525_patternName = DCOMP.__default.escapeVar(((_1524_dtor).dtor_formal).dtor_name);
          DAST._IType _1526_formalType;
          _1526_formalType = ((_1524_dtor).dtor_formal).dtor_typ;
          if (((_1523_j).Sign == 0) && ((_1525_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1521_isNumeric = true;
          }
          if (_1521_isNumeric) {
            _1525_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1524_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1523_j)));
          }
          _1519_hashRhs = (((_1526_formalType).is_Arrow) ? ((_1519_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))) : ((_1519_hashRhs).Then((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1525_patternName), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state")))))));
          _1522_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1522_ctorMatchInner, _1525_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1523_j).Sign == 1) {
            _1518_printRhs = (_1518_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1518_printRhs = (_1518_printRhs).Then(RAST.Expr.create_RawExpr((((_1526_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1525_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1527_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1528_formalTpe;
          RAST._IType _out85;
          _out85 = (this).GenType(_1526_formalType, DCOMP.GenTypeContext.@default());
          _1528_formalTpe = _out85;
          DAST._IType _1529_newFormalType;
          _1529_newFormalType = (_1526_formalType).Replace(_1492_coerceMap);
          RAST._IType _1530_newFormalTpe;
          _1530_newFormalTpe = (_1528_formalTpe).ReplaceMap(_1493_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1531_upcastConverter;
          _1531_upcastConverter = (this).UpcastConversionLambda(_1526_formalType, _1528_formalTpe, _1529_newFormalType, _1530_newFormalTpe, _1494_coerceMapToArg);
          if ((_1531_upcastConverter).is_Success) {
            RAST._IExpr _1532_coercionFunction;
            _1532_coercionFunction = (_1531_upcastConverter).dtor_value;
            _1527_coerceRhsArg = (_1532_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1525_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1523_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1448_datatypeName));
            _1527_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1520_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1520_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1525_patternName, _1527_coerceRhsArg)));
        }
        RAST._IExpr _1533_coerceRhs;
        _1533_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1448_datatypeName)).FSel(DCOMP.__default.escapeName((_1514_ctor).dtor_name)), _1520_coerceRhsArgs);
        if (_1521_isNumeric) {
          _1515_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1515_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1522_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1515_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1515_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1522_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1514_ctor).dtor_hasAnyArgs) {
          _1518_printRhs = (_1518_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1518_printRhs = (_1518_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1510_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1510_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1448_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1515_ctorMatch), RAST.Expr.create_Block(_1518_printRhs))));
        _1511_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1511_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1448_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1515_ctorMatch), RAST.Expr.create_Block(_1519_hashRhs))));
        _1512_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1512_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1448_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1515_ctorMatch), RAST.Expr.create_Block(_1533_coerceRhs))));
      }
      if (((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) && ((new BigInteger((_1462_unusedTypeParams).Count)).Sign == 1)) {
        Dafny.ISequence<RAST._IMatchCase> _1534_extraCases;
        _1534_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1448_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _1510_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1510_printImplBodyCases, _1534_extraCases);
        _1511_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1511_hashImplBodyCases, _1534_extraCases);
        _1512_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1512_coerceImplBodyCases, _1534_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1535_defaultConstrainedTypeParams;
      _1535_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1446_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1536_rTypeParamsDeclsWithEq;
      _1536_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1446_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1537_rTypeParamsDeclsWithHash;
      _1537_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1446_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1538_printImplBody;
      _1538_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1510_printImplBodyCases);
      RAST._IExpr _1539_hashImplBody;
      _1539_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1511_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1446_rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug"))).AsType(), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1448_datatypeName), _1445_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType()))), Std.Wrappers.Option<RAST._IType>.create_Some((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Result"))).AsType()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1446_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1448_datatypeName), _1445_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType())), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1538_printImplBody))))))));
      if ((new BigInteger((_1490_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1540_coerceImplBody;
        _1540_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1512_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1446_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1448_datatypeName), _1445_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1490_rCoerceTypeParams, _1491_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1448_datatypeName), _1445_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1448_datatypeName), _1489_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.__default.SelfOwned)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1448_datatypeName), _1489_coerceTypes)), _1540_coerceImplBody))))))))));
      }
      if (_1509_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1536_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1448_datatypeName), _1445_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1537_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1448_datatypeName), _1445_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))).AsType()))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1539_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1541_structName;
        _1541_structName = (RAST.Expr.create_Identifier(_1448_datatypeName)).FSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1542_structAssignments;
        _1542_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi22 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1543_i = BigInteger.Zero; _1543_i < _hi22; _1543_i++) {
          DAST._IDatatypeDtor _1544_dtor;
          _1544_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1543_i);
          _1542_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1542_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(((_1544_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1545_defaultConstrainedTypeParams;
        _1545_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1446_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1546_fullType;
        _1546_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1448_datatypeName), _1445_rTypeParams);
        if (_1509_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1545_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1546_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1546_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1541_structName, _1542_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1446_rTypeParamsDecls, ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).AsType()).Apply1(_1546_fullType), RAST.Type.create_Borrowed(_1546_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        for (BigInteger _1547_i = BigInteger.Zero; _1547_i < _hi23; _1547_i++) {
          Dafny.ISequence<Dafny.Rune> _1548_name;
          _1548_name = ((p).Select(_1547_i));
          if (escape) {
            _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs55 = DafnyCompilerRustUtils.__default.DafnyNameToContainingPathAndName(_1548_name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1549_modules = _let_tmp_rhs55.dtor__0;
            Dafny.ISequence<Dafny.Rune> _1550_finalName = _let_tmp_rhs55.dtor__1;
            BigInteger _hi24 = new BigInteger((_1549_modules).Count);
            for (BigInteger _1551_j = BigInteger.Zero; _1551_j < _hi24; _1551_j++) {
              r = (r).MSel(DCOMP.__default.escapeName(((_1549_modules).Select(_1551_j))));
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1550_finalName));
          } else {
            r = (r).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1548_name)));
          }
        }
      }
      return r;
    }
    public static RAST._IType GenPathType(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IType t = RAST.Type.Default();
      RAST._IPath _1552_p;
      RAST._IPath _out86;
      _out86 = DCOMP.COMP.GenPath(p, true);
      _1552_p = _out86;
      t = (_1552_p).AsType();
      return t;
    }
    public static RAST._IExpr GenPathExpr(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p, bool escape)
    {
      RAST._IExpr e = RAST.Expr.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        e = RAST.__default.self;
        return e;
      }
      RAST._IPath _1553_p;
      RAST._IPath _out87;
      _out87 = DCOMP.COMP.GenPath(p, escape);
      _1553_p = _out87;
      e = (_1553_p).AsExpr();
      return e;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi25 = new BigInteger((args).Count);
      for (BigInteger _1554_i = BigInteger.Zero; _1554_i < _hi25; _1554_i++) {
        RAST._IType _1555_genTp;
        RAST._IType _out88;
        _out88 = (this).GenType((args).Select(_1554_i), genTypeContext);
        _1555_genTp = _out88;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1555_genTp));
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, bool genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source76 = c;
      bool unmatched76 = true;
      if (unmatched76) {
        if (_source76.is_UserDefined) {
          DAST._IResolvedType _1556_resolved = _source76.dtor_resolved;
          unmatched76 = false;
          {
            RAST._IType _1557_t;
            RAST._IType _out89;
            _out89 = DCOMP.COMP.GenPathType((_1556_resolved).dtor_path);
            _1557_t = _out89;
            Dafny.ISequence<RAST._IType> _1558_typeArgs;
            Dafny.ISequence<RAST._IType> _out90;
            _out90 = (this).GenTypeArgs((_1556_resolved).dtor_typeArgs, false);
            _1558_typeArgs = _out90;
            s = RAST.Type.create_TypeApp(_1557_t, _1558_typeArgs);
            DAST._IResolvedTypeBase _source77 = (_1556_resolved).dtor_kind;
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
                  if ((this).IsRcWrapped((_1556_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched77) {
              if (_source77.is_Trait) {
                unmatched77 = false;
                {
                  if (((_1556_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = RAST.__default.AnyTrait;
                  }
                  if (!((genTypeContext))) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched77) {
              DAST._IType _1559_base = _source77.dtor_baseType;
              DAST._INewtypeRange _1560_range = _source77.dtor_range;
              bool _1561_erased = _source77.dtor_erase;
              unmatched77 = false;
              {
                if (_1561_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source78 = DCOMP.COMP.NewtypeRangeToRustType(_1560_range);
                  bool unmatched78 = true;
                  if (unmatched78) {
                    if (_source78.is_Some) {
                      RAST._IType _1562_v = _source78.dtor_value;
                      unmatched78 = false;
                      s = _1562_v;
                    }
                  }
                  if (unmatched78) {
                    unmatched78 = false;
                    RAST._IType _1563_underlying;
                    RAST._IType _out91;
                    _out91 = (this).GenType(_1559_base, DCOMP.GenTypeContext.@default());
                    _1563_underlying = _out91;
                    s = RAST.Type.create_TSynonym(s, _1563_underlying);
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
            if (!((genTypeContext))) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1564_types = _source76.dtor_Tuple_a0;
          unmatched76 = false;
          {
            Dafny.ISequence<RAST._IType> _1565_args;
            _1565_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1566_i;
            _1566_i = BigInteger.Zero;
            while ((_1566_i) < (new BigInteger((_1564_types).Count))) {
              RAST._IType _1567_generated;
              RAST._IType _out92;
              _out92 = (this).GenType((_1564_types).Select(_1566_i), false);
              _1567_generated = _out92;
              _1565_args = Dafny.Sequence<RAST._IType>.Concat(_1565_args, Dafny.Sequence<RAST._IType>.FromElements(_1567_generated));
              _1566_i = (_1566_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1564_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1565_args)) : (RAST.__default.SystemTupleType(_1565_args)));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Array) {
          DAST._IType _1568_element = _source76.dtor_element;
          BigInteger _1569_dims = _source76.dtor_dims;
          unmatched76 = false;
          {
            if ((_1569_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1570_elem;
              RAST._IType _out93;
              _out93 = (this).GenType(_1568_element, false);
              _1570_elem = _out93;
              if ((_1569_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1570_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1571_n;
                _1571_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1569_dims));
                s = (((RAST.__default.dafny__runtime).MSel(_1571_n)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1570_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Seq) {
          DAST._IType _1572_element = _source76.dtor_element;
          unmatched76 = false;
          {
            RAST._IType _1573_elem;
            RAST._IType _out94;
            _out94 = (this).GenType(_1572_element, false);
            _1573_elem = _out94;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1573_elem));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Set) {
          DAST._IType _1574_element = _source76.dtor_element;
          unmatched76 = false;
          {
            RAST._IType _1575_elem;
            RAST._IType _out95;
            _out95 = (this).GenType(_1574_element, false);
            _1575_elem = _out95;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1575_elem));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Multiset) {
          DAST._IType _1576_element = _source76.dtor_element;
          unmatched76 = false;
          {
            RAST._IType _1577_elem;
            RAST._IType _out96;
            _out96 = (this).GenType(_1576_element, false);
            _1577_elem = _out96;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1577_elem));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Map) {
          DAST._IType _1578_key = _source76.dtor_key;
          DAST._IType _1579_value = _source76.dtor_value;
          unmatched76 = false;
          {
            RAST._IType _1580_keyType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1578_key, false);
            _1580_keyType = _out97;
            RAST._IType _1581_valueType;
            RAST._IType _out98;
            _out98 = (this).GenType(_1579_value, genTypeContext);
            _1581_valueType = _out98;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1580_keyType, _1581_valueType));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_MapBuilder) {
          DAST._IType _1582_key = _source76.dtor_key;
          DAST._IType _1583_value = _source76.dtor_value;
          unmatched76 = false;
          {
            RAST._IType _1584_keyType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1582_key, false);
            _1584_keyType = _out99;
            RAST._IType _1585_valueType;
            RAST._IType _out100;
            _out100 = (this).GenType(_1583_value, genTypeContext);
            _1585_valueType = _out100;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1584_keyType, _1585_valueType));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_SetBuilder) {
          DAST._IType _1586_elem = _source76.dtor_element;
          unmatched76 = false;
          {
            RAST._IType _1587_elemType;
            RAST._IType _out101;
            _out101 = (this).GenType(_1586_elem, false);
            _1587_elemType = _out101;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1587_elemType));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1588_args = _source76.dtor_args;
          DAST._IType _1589_result = _source76.dtor_result;
          unmatched76 = false;
          {
            Dafny.ISequence<RAST._IType> _1590_argTypes;
            _1590_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1591_i;
            _1591_i = BigInteger.Zero;
            while ((_1591_i) < (new BigInteger((_1588_args).Count))) {
              RAST._IType _1592_generated;
              RAST._IType _out102;
              _out102 = (this).GenType((_1588_args).Select(_1591_i), false);
              _1592_generated = _out102;
              _1590_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1590_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1592_generated)));
              _1591_i = (_1591_i) + (BigInteger.One);
            }
            RAST._IType _1593_resultType;
            RAST._IType _out103;
            _out103 = (this).GenType(_1589_result, DCOMP.GenTypeContext.@default());
            _1593_resultType = _out103;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1590_argTypes, _1593_resultType)));
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source76.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1594_name = _h90;
          unmatched76 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1594_name));
        }
      }
      if (unmatched76) {
        if (_source76.is_Primitive) {
          DAST._IPrimitive _1595_p = _source76.dtor_Primitive_a0;
          unmatched76 = false;
          {
            DAST._IPrimitive _source79 = _1595_p;
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
        Dafny.ISequence<Dafny.Rune> _1596_v = _source76.dtor_Passthrough_a0;
        unmatched76 = false;
        s = RAST.__default.RawType(_1596_v);
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
      for (BigInteger _1597_i = BigInteger.Zero; _1597_i < _hi26; _1597_i++) {
        DAST._IMethod _source80 = (body).Select(_1597_i);
        bool unmatched80 = true;
        if (unmatched80) {
          DAST._IMethod _1598_m = _source80;
          unmatched80 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source81 = (_1598_m).dtor_overridingPath;
            bool unmatched81 = true;
            if (unmatched81) {
              if (_source81.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1599_p = _source81.dtor_value;
                unmatched81 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1600_existing;
                  _1600_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1599_p)) {
                    _1600_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1599_p);
                  }
                  if (((new BigInteger(((_1598_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1601_genMethod;
                  RAST._IImplMember _out104;
                  _out104 = (this).GenMethod(_1598_m, true, enclosingType, enclosingTypeParams);
                  _1601_genMethod = _out104;
                  _1600_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1600_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1601_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1599_p, _1600_existing)));
                }
              }
            }
            if (unmatched81) {
              unmatched81 = false;
              {
                RAST._IImplMember _1602_generated;
                RAST._IImplMember _out105;
                _out105 = (this).GenMethod(_1598_m, forTrait, enclosingType, enclosingTypeParams);
                _1602_generated = _out105;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1602_generated));
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
      for (BigInteger _1603_i = BigInteger.Zero; _1603_i < _hi27; _1603_i++) {
        DAST._IFormal _1604_param;
        _1604_param = (@params).Select(_1603_i);
        RAST._IType _1605_paramType;
        RAST._IType _out106;
        _out106 = (this).GenType((_1604_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1605_paramType = _out106;
        if (((!((_1605_paramType).CanReadWithoutClone())) || (forLambda)) && (!((_1604_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1605_paramType = RAST.Type.create_Borrowed(_1605_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeVar((_1604_param).dtor_name), _1605_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1606_params;
      Dafny.ISequence<RAST._IFormal> _out107;
      _out107 = (this).GenParams((m).dtor_params, false);
      _1606_params = _out107;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1607_paramNames;
      _1607_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1608_paramTypes;
      _1608_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1609_paramI = BigInteger.Zero; _1609_paramI < _hi28; _1609_paramI++) {
        DAST._IFormal _1610_dafny__formal;
        _1610_dafny__formal = ((m).dtor_params).Select(_1609_paramI);
        RAST._IFormal _1611_formal;
        _1611_formal = (_1606_params).Select(_1609_paramI);
        Dafny.ISequence<Dafny.Rune> _1612_name;
        _1612_name = (_1611_formal).dtor_name;
        _1607_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1607_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1612_name));
        _1608_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1608_paramTypes, _1612_name, (_1611_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1613_fnName;
      _1613_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1614_selfIdent;
      _1614_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1615_selfId;
        _1615_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1615_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv190 = enclosingTypeParams;
        var _pat_let_tv191 = enclosingType;
        DAST._IType _1616_instanceType;
        _1616_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source82 = enclosingType;
          bool unmatched82 = true;
          if (unmatched82) {
            if (_source82.is_UserDefined) {
              DAST._IResolvedType _1617_r = _source82.dtor_resolved;
              unmatched82 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1617_r, _pat_let22_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let22_0, _1618_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv190, _pat_let23_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let23_0, _1619_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1618_dt__update__tmp_h0).dtor_path, _1619_dt__update_htypeArgs_h0, (_1618_dt__update__tmp_h0).dtor_kind, (_1618_dt__update__tmp_h0).dtor_attributes, (_1618_dt__update__tmp_h0).dtor_properMethods, (_1618_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched82) {
            unmatched82 = false;
            return _pat_let_tv191;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1620_selfFormal;
          _1620_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1606_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1620_selfFormal), _1606_params);
        } else {
          RAST._IType _1621_tpe;
          RAST._IType _out108;
          _out108 = (this).GenType(_1616_instanceType, DCOMP.GenTypeContext.@default());
          _1621_tpe = _out108;
          if ((_1615_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            if (((this).ObjectType).is_RcMut) {
              _1621_tpe = RAST.Type.create_Borrowed(_1621_tpe);
            }
          } else if ((_1615_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1621_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1621_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1621_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _1621_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.__default.SelfOwned));
              } else {
                _1621_tpe = RAST.Type.create_Borrowed(RAST.__default.SelfOwned);
              }
            }
          }
          _1606_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1615_selfId, _1621_tpe)), _1606_params);
        }
        _1614_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1615_selfId, _1616_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1622_retTypeArgs;
      _1622_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1623_typeI;
      _1623_typeI = BigInteger.Zero;
      while ((_1623_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1624_typeExpr;
        RAST._IType _out109;
        _out109 = (this).GenType(((m).dtor_outTypes).Select(_1623_typeI), DCOMP.GenTypeContext.@default());
        _1624_typeExpr = _out109;
        _1622_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1622_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1624_typeExpr));
        _1623_typeI = (_1623_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1625_visibility;
      _1625_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1626_typeParamsFiltered;
      _1626_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi29 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1627_typeParamI = BigInteger.Zero; _1627_typeParamI < _hi29; _1627_typeParamI++) {
        DAST._ITypeArgDecl _1628_typeParam;
        _1628_typeParam = ((m).dtor_typeParams).Select(_1627_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1628_typeParam).dtor_name)))) {
          _1626_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1626_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1628_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1629_typeParams;
      _1629_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1626_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi30 = new BigInteger((_1626_typeParamsFiltered).Count);
        for (BigInteger _1630_i = BigInteger.Zero; _1630_i < _hi30; _1630_i++) {
          DAST._IType _1631_typeArg;
          RAST._ITypeParamDecl _1632_rTypeParamDecl;
          DAST._IType _out110;
          RAST._ITypeParamDecl _out111;
          (this).GenTypeParam((_1626_typeParamsFiltered).Select(_1630_i), out _out110, out _out111);
          _1631_typeArg = _out110;
          _1632_rTypeParamDecl = _out111;
          var _pat_let_tv192 = _1632_rTypeParamDecl;
          _1632_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1632_rTypeParamDecl, _pat_let24_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let24_0, _1633_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>((_pat_let_tv192).dtor_constraints, _pat_let25_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let25_0, _1634_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1633_dt__update__tmp_h1).dtor_name, _1634_dt__update_hconstraints_h0)))));
          _1629_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1629_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1632_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1635_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1636_env = DCOMP.Environment.Default();
      RAST._IExpr _1637_preBody;
      _1637_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1638_preAssignNames;
      _1638_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1639_preAssignTypes;
      _1639_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1640_earlyReturn;
        _1640_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source83 = (m).dtor_outVars;
        bool unmatched83 = true;
        if (unmatched83) {
          if (_source83.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1641_outVars = _source83.dtor_value;
            unmatched83 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1640_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi31 = new BigInteger((_1641_outVars).Count);
                for (BigInteger _1642_outI = BigInteger.Zero; _1642_outI < _hi31; _1642_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1643_outVar;
                  _1643_outVar = (_1641_outVars).Select(_1642_outI);
                  Dafny.ISequence<Dafny.Rune> _1644_outName;
                  _1644_outName = DCOMP.__default.escapeVar(_1643_outVar);
                  Dafny.ISequence<Dafny.Rune> _1645_tracker__name;
                  _1645_tracker__name = DCOMP.__default.AddAssignedPrefix(_1644_outName);
                  _1638_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1638_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1645_tracker__name));
                  _1639_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1639_preAssignTypes, _1645_tracker__name, RAST.Type.create_Bool());
                  _1637_preBody = (_1637_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1645_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1646_tupleArgs;
                _1646_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi32 = new BigInteger((_1641_outVars).Count);
                for (BigInteger _1647_outI = BigInteger.Zero; _1647_outI < _hi32; _1647_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1648_outVar;
                  _1648_outVar = (_1641_outVars).Select(_1647_outI);
                  RAST._IType _1649_outType;
                  RAST._IType _out112;
                  _out112 = (this).GenType(((m).dtor_outTypes).Select(_1647_outI), DCOMP.GenTypeContext.@default());
                  _1649_outType = _out112;
                  Dafny.ISequence<Dafny.Rune> _1650_outName;
                  _1650_outName = DCOMP.__default.escapeVar(_1648_outVar);
                  _1607_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1607_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1650_outName));
                  RAST._IType _1651_outMaybeType;
                  _1651_outMaybeType = (((_1649_outType).CanReadWithoutClone()) ? (_1649_outType) : (RAST.__default.MaybePlaceboType(_1649_outType)));
                  _1608_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1608_paramTypes, _1650_outName, _1651_outMaybeType);
                  _1646_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1646_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1650_outName));
                }
                _1640_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_1646_tupleArgs);
              }
            }
          }
        }
        if (unmatched83) {
          unmatched83 = false;
        }
        _1636_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1638_preAssignNames, _1607_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1639_preAssignTypes, _1608_paramTypes));
        RAST._IExpr _1652_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1653___v71;
        DCOMP._IEnvironment _1654___v72;
        RAST._IExpr _out113;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out114;
        DCOMP._IEnvironment _out115;
        (this).GenStmts((m).dtor_body, _1614_selfIdent, _1636_env, true, _1640_earlyReturn, out _out113, out _out114, out _out115);
        _1652_body = _out113;
        _1653___v71 = _out114;
        _1654___v72 = _out115;
        _1635_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1637_preBody).Then(_1652_body));
      } else {
        _1636_env = DCOMP.Environment.create(_1607_paramNames, _1608_paramTypes);
        _1635_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1625_visibility, RAST.Fn.create(_1613_fnName, _1629_typeParams, _1606_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1622_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1622_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1622_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1635_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1655_declarations;
      _1655_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1656_i;
      _1656_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1657_stmts;
      _1657_stmts = stmts;
      while ((_1656_i) < (new BigInteger((_1657_stmts).Count))) {
        DAST._IStatement _1658_stmt;
        _1658_stmt = (_1657_stmts).Select(_1656_i);
        DAST._IStatement _source84 = _1658_stmt;
        bool unmatched84 = true;
        if (unmatched84) {
          if (_source84.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1659_name = _source84.dtor_name;
            DAST._IType _1660_optType = _source84.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source84.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched84 = false;
              if (((_1656_i) + (BigInteger.One)) < (new BigInteger((_1657_stmts).Count))) {
                DAST._IStatement _source85 = (_1657_stmts).Select((_1656_i) + (BigInteger.One));
                bool unmatched85 = true;
                if (unmatched85) {
                  if (_source85.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source85.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> _1661_name2 = lhs0.dtor_ident;
                      DAST._IExpression _1662_rhs = _source85.dtor_value;
                      unmatched85 = false;
                      if (object.Equals(_1661_name2, _1659_name)) {
                        _1657_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1657_stmts).Subsequence(BigInteger.Zero, _1656_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1659_name, _1660_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1662_rhs)))), (_1657_stmts).Drop((_1656_i) + (new BigInteger(2))));
                        _1658_stmt = (_1657_stmts).Select(_1656_i);
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
        RAST._IExpr _1663_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1664_recIdents;
        DCOMP._IEnvironment _1665_newEnv2;
        RAST._IExpr _out116;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
        DCOMP._IEnvironment _out118;
        (this).GenStmt(_1658_stmt, selfIdent, newEnv, (isLast) && ((_1656_i) == ((new BigInteger((_1657_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out116, out _out117, out _out118);
        _1663_stmtExpr = _out116;
        _1664_recIdents = _out117;
        _1665_newEnv2 = _out118;
        newEnv = _1665_newEnv2;
        DAST._IStatement _source86 = _1658_stmt;
        bool unmatched86 = true;
        if (unmatched86) {
          if (_source86.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1666_name = _source86.dtor_name;
            unmatched86 = false;
            {
              _1655_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1655_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_1666_name)));
            }
          }
        }
        if (unmatched86) {
          unmatched86 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1664_recIdents, _1655_declarations));
        generated = (generated).Then(_1663_stmtExpr);
        _1656_i = (_1656_i) + (BigInteger.One);
        if ((_1663_stmtExpr).is_Return) {
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
          Dafny.ISequence<Dafny.Rune> _1667_id = _source87.dtor_ident;
          unmatched87 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1668_idRust;
            _1668_idRust = DCOMP.__default.escapeVar(_1667_id);
            if (((env).IsBorrowed(_1668_idRust)) || ((env).IsBorrowedMut(_1668_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1668_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1668_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1668_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Select) {
          DAST._IExpression _1669_on = _source87.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1670_field = _source87.dtor_field;
          unmatched87 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1671_fieldName;
            _1671_fieldName = DCOMP.__default.escapeVar(_1670_field);
            RAST._IExpr _1672_onExpr;
            DCOMP._IOwnership _1673_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1674_recIdents;
            RAST._IExpr _out119;
            DCOMP._IOwnership _out120;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
            (this).GenExpr(_1669_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out119, out _out120, out _out121);
            _1672_onExpr = _out119;
            _1673_onOwned = _out120;
            _1674_recIdents = _out121;
            RAST._IExpr _source88 = _1672_onExpr;
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
                Dafny.ISequence<Dafny.Rune> _1675_isAssignedVar;
                _1675_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1671_fieldName);
                if (((newEnv).dtor_names).Contains(_1675_isAssignedVar)) {
                  generated = (((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1671_fieldName), RAST.Expr.create_Identifier(_1675_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1675_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1675_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1671_fieldName, rhs);
                }
              }
            }
            if (unmatched88) {
              unmatched88 = false;
              if (!object.Equals(_1672_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1672_onExpr = ((this).modify__macro).Apply1(_1672_onExpr);
              }
              generated = RAST.__default.AssignMember(_1672_onExpr, _1671_fieldName, rhs);
            }
            readIdents = _1674_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched87) {
        DAST._IExpression _1676_on = _source87.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1677_indices = _source87.dtor_indices;
        unmatched87 = false;
        {
          RAST._IExpr _1678_onExpr;
          DCOMP._IOwnership _1679_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1680_recIdents;
          RAST._IExpr _out122;
          DCOMP._IOwnership _out123;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
          (this).GenExpr(_1676_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out122, out _out123, out _out124);
          _1678_onExpr = _out122;
          _1679_onOwned = _out123;
          _1680_recIdents = _out124;
          readIdents = _1680_recIdents;
          _1678_onExpr = ((this).modify__macro).Apply1(_1678_onExpr);
          RAST._IExpr _1681_r;
          _1681_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1682_indicesExpr;
          _1682_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi33 = new BigInteger((_1677_indices).Count);
          for (BigInteger _1683_i = BigInteger.Zero; _1683_i < _hi33; _1683_i++) {
            RAST._IExpr _1684_idx;
            DCOMP._IOwnership _1685___v81;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1686_recIdentsIdx;
            RAST._IExpr _out125;
            DCOMP._IOwnership _out126;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out127;
            (this).GenExpr((_1677_indices).Select(_1683_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out125, out _out126, out _out127);
            _1684_idx = _out125;
            _1685___v81 = _out126;
            _1686_recIdentsIdx = _out127;
            Dafny.ISequence<Dafny.Rune> _1687_varName;
            _1687_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1683_i));
            _1682_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1682_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1687_varName)));
            _1681_r = (_1681_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1687_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1684_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1686_recIdentsIdx);
          }
          if ((new BigInteger((_1677_indices).Count)) > (BigInteger.One)) {
            _1678_onExpr = (_1678_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1688_rhs;
          _1688_rhs = rhs;
          var _pat_let_tv193 = env;
          if (((_1678_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1678_onExpr).LhsIdentifierName(), _pat_let26_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let26_0, _1689_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv193).GetType(_1689_name), _pat_let27_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let27_0, _1690_tpe => ((_1690_tpe).is_Some) && (((_1690_tpe).dtor_value).IsUninitArray())))))))) {
            _1688_rhs = RAST.__default.MaybeUninitNew(_1688_rhs);
          }
          generated = (_1681_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1678_onExpr, _1682_indicesExpr)), _1688_rhs));
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
          Dafny.ISequence<DAST._IFormal> _1691_fields = _source89.dtor_fields;
          unmatched89 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi34 = new BigInteger((_1691_fields).Count);
            for (BigInteger _1692_i = BigInteger.Zero; _1692_i < _hi34; _1692_i++) {
              DAST._IFormal _1693_field;
              _1693_field = (_1691_fields).Select(_1692_i);
              Dafny.ISequence<Dafny.Rune> _1694_fieldName;
              _1694_fieldName = DCOMP.__default.escapeVar((_1693_field).dtor_name);
              RAST._IType _1695_fieldTyp;
              RAST._IType _out128;
              _out128 = (this).GenType((_1693_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1695_fieldTyp = _out128;
              Dafny.ISequence<Dafny.Rune> _1696_isAssignedVar;
              _1696_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1694_fieldName);
              if (((newEnv).dtor_names).Contains(_1696_isAssignedVar)) {
                RAST._IExpr _1697_rhs;
                DCOMP._IOwnership _1698___v82;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1699___v83;
                RAST._IExpr _out129;
                DCOMP._IOwnership _out130;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1693_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out129, out _out130, out _out131);
                _1697_rhs = _out129;
                _1698___v82 = _out130;
                _1699___v83 = _out131;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1696_isAssignedVar));
                generated = (generated).Then((((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1694_fieldName), RAST.Expr.create_Identifier(_1696_isAssignedVar), _1697_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1696_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1700_name = _source89.dtor_name;
          DAST._IType _1701_typ = _source89.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source89.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1702_expression = maybeValue1.dtor_value;
            unmatched89 = false;
            {
              RAST._IType _1703_tpe;
              RAST._IType _out132;
              _out132 = (this).GenType(_1701_typ, DCOMP.GenTypeContext.@default());
              _1703_tpe = _out132;
              Dafny.ISequence<Dafny.Rune> _1704_varName;
              _1704_varName = DCOMP.__default.escapeVar(_1700_name);
              bool _1705_hasCopySemantics;
              _1705_hasCopySemantics = (_1703_tpe).CanReadWithoutClone();
              if (((_1702_expression).is_InitializationValue) && (!(_1705_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1704_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.MaybePlaceboPath).AsExpr()).ApplyType1(_1703_tpe)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1704_varName, RAST.__default.MaybePlaceboType(_1703_tpe));
              } else {
                RAST._IExpr _1706_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1707_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1702_expression).is_InitializationValue) && ((_1703_tpe).IsObjectOrPointer())) {
                  _1706_expr = (_1703_tpe).ToNullExpr();
                  _1707_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1708_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out133;
                  DCOMP._IOwnership _out134;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
                  (this).GenExpr(_1702_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
                  _1706_expr = _out133;
                  _1708_exprOwnership = _out134;
                  _1707_recIdents = _out135;
                }
                readIdents = _1707_recIdents;
                _1703_tpe = (((_1702_expression).is_NewUninitArray) ? ((_1703_tpe).TypeAtInitialization()) : (_1703_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1704_varName, Std.Wrappers.Option<RAST._IType>.create_Some(_1703_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1706_expr));
                newEnv = (env).AddAssigned(_1704_varName, _1703_tpe);
              }
            }
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1709_name = _source89.dtor_name;
          DAST._IType _1710_typ = _source89.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source89.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched89 = false;
            {
              DAST._IStatement _1711_newStmt;
              _1711_newStmt = DAST.Statement.create_DeclareVar(_1709_name, _1710_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1710_typ)));
              RAST._IExpr _out136;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
              DCOMP._IEnvironment _out138;
              (this).GenStmt(_1711_newStmt, selfIdent, env, isLast, earlyReturn, out _out136, out _out137, out _out138);
              generated = _out136;
              readIdents = _out137;
              newEnv = _out138;
            }
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Assign) {
          DAST._IAssignLhs _1712_lhs = _source89.dtor_lhs;
          DAST._IExpression _1713_expression = _source89.dtor_value;
          unmatched89 = false;
          {
            RAST._IExpr _1714_exprGen;
            DCOMP._IOwnership _1715___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1716_exprIdents;
            RAST._IExpr _out139;
            DCOMP._IOwnership _out140;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
            (this).GenExpr(_1713_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out139, out _out140, out _out141);
            _1714_exprGen = _out139;
            _1715___v84 = _out140;
            _1716_exprIdents = _out141;
            if ((_1712_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1717_rustId;
              _1717_rustId = DCOMP.__default.escapeVar((_1712_lhs).dtor_ident);
              Std.Wrappers._IOption<RAST._IType> _1718_tpe;
              _1718_tpe = (env).GetType(_1717_rustId);
              if (((_1718_tpe).is_Some) && ((((_1718_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1714_exprGen = RAST.__default.MaybePlacebo(_1714_exprGen);
              }
            }
            if (((_1712_lhs).is_Index) && (((_1712_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1719_rustId;
              _1719_rustId = DCOMP.__default.escapeVar(((_1712_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1720_tpe;
              _1720_tpe = (env).GetType(_1719_rustId);
              if (((_1720_tpe).is_Some) && ((((_1720_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1714_exprGen = RAST.__default.MaybeUninitNew(_1714_exprGen);
              }
            }
            RAST._IExpr _1721_lhsGen;
            bool _1722_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1723_recIdents;
            DCOMP._IEnvironment _1724_resEnv;
            RAST._IExpr _out142;
            bool _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            DCOMP._IEnvironment _out145;
            (this).GenAssignLhs(_1712_lhs, _1714_exprGen, selfIdent, env, out _out142, out _out143, out _out144, out _out145);
            _1721_lhsGen = _out142;
            _1722_needsIIFE = _out143;
            _1723_recIdents = _out144;
            _1724_resEnv = _out145;
            generated = _1721_lhsGen;
            newEnv = _1724_resEnv;
            if (_1722_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1723_recIdents, _1716_exprIdents);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_If) {
          DAST._IExpression _1725_cond = _source89.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1726_thnDafny = _source89.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1727_elsDafny = _source89.dtor_els;
          unmatched89 = false;
          {
            RAST._IExpr _1728_cond;
            DCOMP._IOwnership _1729___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1730_recIdents;
            RAST._IExpr _out146;
            DCOMP._IOwnership _out147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
            (this).GenExpr(_1725_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out146, out _out147, out _out148);
            _1728_cond = _out146;
            _1729___v85 = _out147;
            _1730_recIdents = _out148;
            Dafny.ISequence<Dafny.Rune> _1731_condString;
            _1731_condString = (_1728_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1730_recIdents;
            RAST._IExpr _1732_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1733_thnIdents;
            DCOMP._IEnvironment _1734_thnEnv;
            RAST._IExpr _out149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out150;
            DCOMP._IEnvironment _out151;
            (this).GenStmts(_1726_thnDafny, selfIdent, env, isLast, earlyReturn, out _out149, out _out150, out _out151);
            _1732_thn = _out149;
            _1733_thnIdents = _out150;
            _1734_thnEnv = _out151;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1733_thnIdents);
            RAST._IExpr _1735_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1736_elsIdents;
            DCOMP._IEnvironment _1737_elsEnv;
            RAST._IExpr _out152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
            DCOMP._IEnvironment _out154;
            (this).GenStmts(_1727_elsDafny, selfIdent, env, isLast, earlyReturn, out _out152, out _out153, out _out154);
            _1735_els = _out152;
            _1736_elsIdents = _out153;
            _1737_elsEnv = _out154;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1736_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1728_cond, _1732_thn, _1735_els);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1738_lbl = _source89.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1739_body = _source89.dtor_body;
          unmatched89 = false;
          {
            RAST._IExpr _1740_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1741_bodyIdents;
            DCOMP._IEnvironment _1742_env2;
            RAST._IExpr _out155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
            DCOMP._IEnvironment _out157;
            (this).GenStmts(_1739_body, selfIdent, env, isLast, earlyReturn, out _out155, out _out156, out _out157);
            _1740_body = _out155;
            _1741_bodyIdents = _out156;
            _1742_env2 = _out157;
            readIdents = _1741_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1738_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1740_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_While) {
          DAST._IExpression _1743_cond = _source89.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1744_body = _source89.dtor_body;
          unmatched89 = false;
          {
            RAST._IExpr _1745_cond;
            DCOMP._IOwnership _1746___v86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1747_recIdents;
            RAST._IExpr _out158;
            DCOMP._IOwnership _out159;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
            (this).GenExpr(_1743_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out158, out _out159, out _out160);
            _1745_cond = _out158;
            _1746___v86 = _out159;
            _1747_recIdents = _out160;
            readIdents = _1747_recIdents;
            RAST._IExpr _1748_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1749_bodyIdents;
            DCOMP._IEnvironment _1750_bodyEnv;
            RAST._IExpr _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            DCOMP._IEnvironment _out163;
            (this).GenStmts(_1744_body, selfIdent, env, false, earlyReturn, out _out161, out _out162, out _out163);
            _1748_bodyExpr = _out161;
            _1749_bodyIdents = _out162;
            _1750_bodyEnv = _out163;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1749_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1745_cond), _1748_bodyExpr);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1751_boundName = _source89.dtor_boundName;
          DAST._IType _1752_boundType = _source89.dtor_boundType;
          DAST._IExpression _1753_overExpr = _source89.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1754_body = _source89.dtor_body;
          unmatched89 = false;
          {
            RAST._IExpr _1755_over;
            DCOMP._IOwnership _1756___v87;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1757_recIdents;
            RAST._IExpr _out164;
            DCOMP._IOwnership _out165;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out166;
            (this).GenExpr(_1753_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out164, out _out165, out _out166);
            _1755_over = _out164;
            _1756___v87 = _out165;
            _1757_recIdents = _out166;
            if (((_1753_overExpr).is_MapBoundedPool) || ((_1753_overExpr).is_SetBoundedPool)) {
              _1755_over = ((_1755_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1758_boundTpe;
            RAST._IType _out167;
            _out167 = (this).GenType(_1752_boundType, DCOMP.GenTypeContext.@default());
            _1758_boundTpe = _out167;
            readIdents = _1757_recIdents;
            Dafny.ISequence<Dafny.Rune> _1759_boundRName;
            _1759_boundRName = DCOMP.__default.escapeVar(_1751_boundName);
            RAST._IExpr _1760_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1761_bodyIdents;
            DCOMP._IEnvironment _1762_bodyEnv;
            RAST._IExpr _out168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
            DCOMP._IEnvironment _out170;
            (this).GenStmts(_1754_body, selfIdent, (env).AddAssigned(_1759_boundRName, _1758_boundTpe), false, earlyReturn, out _out168, out _out169, out _out170);
            _1760_bodyExpr = _out168;
            _1761_bodyIdents = _out169;
            _1762_bodyEnv = _out170;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1761_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1759_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1759_boundRName, _1755_over, _1760_bodyExpr);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1763_toLabel = _source89.dtor_toLabel;
          unmatched89 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source90 = _1763_toLabel;
            bool unmatched90 = true;
            if (unmatched90) {
              if (_source90.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1764_lbl = _source90.dtor_value;
                unmatched90 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1764_lbl)));
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
          Dafny.ISequence<DAST._IStatement> _1765_body = _source89.dtor_body;
          unmatched89 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1766_selfClone;
              DCOMP._IOwnership _1767___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1768___v89;
              RAST._IExpr _out171;
              DCOMP._IOwnership _out172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out171, out _out172, out _out173);
              _1766_selfClone = _out171;
              _1767___v88 = _out172;
              _1768___v89 = _out173;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1766_selfClone)));
            }
            newEnv = env;
            BigInteger _hi35 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1769_paramI = BigInteger.Zero; _1769_paramI < _hi35; _1769_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1770_param;
              _1770_param = ((env).dtor_names).Select(_1769_paramI);
              RAST._IExpr _1771_paramInit;
              DCOMP._IOwnership _1772___v90;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1773___v91;
              RAST._IExpr _out174;
              DCOMP._IOwnership _out175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out176;
              (this).GenIdent(_1770_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out174, out _out175, out _out176);
              _1771_paramInit = _out174;
              _1772___v90 = _out175;
              _1773___v91 = _out176;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1770_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1771_paramInit)));
              if (((env).dtor_types).Contains(_1770_param)) {
                RAST._IType _1774_declaredType;
                _1774_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1770_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1770_param, _1774_declaredType);
              }
            }
            RAST._IExpr _1775_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1776_bodyIdents;
            DCOMP._IEnvironment _1777_bodyEnv;
            RAST._IExpr _out177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out178;
            DCOMP._IEnvironment _out179;
            (this).GenStmts(_1765_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out177, out _out178, out _out179);
            _1775_bodyExpr = _out177;
            _1776_bodyIdents = _out178;
            _1777_bodyEnv = _out179;
            readIdents = _1776_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1775_bodyExpr)));
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
          DAST._IExpression _1778_on = _source89.dtor_on;
          DAST._ICallName _1779_name = _source89.dtor_callName;
          Dafny.ISequence<DAST._IType> _1780_typeArgs = _source89.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1781_args = _source89.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1782_maybeOutVars = _source89.dtor_outs;
          unmatched89 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1783_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1784_recIdents;
            Dafny.ISequence<RAST._IType> _1785_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1786_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out181;
            Dafny.ISequence<RAST._IType> _out182;
            Std.Wrappers._IOption<DAST._IResolvedType> _out183;
            (this).GenArgs(selfIdent, _1779_name, _1780_typeArgs, _1781_args, env, out _out180, out _out181, out _out182, out _out183);
            _1783_argExprs = _out180;
            _1784_recIdents = _out181;
            _1785_typeExprs = _out182;
            _1786_fullNameQualifier = _out183;
            readIdents = _1784_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source91 = _1786_fullNameQualifier;
            bool unmatched91 = true;
            if (unmatched91) {
              if (_source91.is_Some) {
                DAST._IResolvedType value9 = _source91.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1787_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1788_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1789_base = value9.dtor_kind;
                unmatched91 = false;
                RAST._IExpr _1790_fullPath;
                RAST._IExpr _out184;
                _out184 = DCOMP.COMP.GenPathExpr(_1787_path, true);
                _1790_fullPath = _out184;
                Dafny.ISequence<RAST._IType> _1791_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out185;
                _out185 = (this).GenTypeArgs(_1788_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1791_onTypeExprs = _out185;
                RAST._IExpr _1792_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1793_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1794_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1789_base).is_Trait) || ((_1789_base).is_Class)) {
                  RAST._IExpr _out186;
                  DCOMP._IOwnership _out187;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out188;
                  (this).GenExpr(_1778_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out186, out _out187, out _out188);
                  _1792_onExpr = _out186;
                  _1793_recOwnership = _out187;
                  _1794_recIdents = _out188;
                  _1792_onExpr = ((this).modify__macro).Apply1(_1792_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1794_recIdents);
                } else {
                  RAST._IExpr _out189;
                  DCOMP._IOwnership _out190;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out191;
                  (this).GenExpr(_1778_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out189, out _out190, out _out191);
                  _1792_onExpr = _out189;
                  _1793_recOwnership = _out190;
                  _1794_recIdents = _out191;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1794_recIdents);
                }
                generated = ((((_1790_fullPath).ApplyType(_1791_onTypeExprs)).FSel(DCOMP.__default.escapeName((_1779_name).dtor_name))).ApplyType(_1785_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1792_onExpr), _1783_argExprs));
              }
            }
            if (unmatched91) {
              unmatched91 = false;
              RAST._IExpr _1795_onExpr;
              DCOMP._IOwnership _1796___v96;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1797_enclosingIdents;
              RAST._IExpr _out192;
              DCOMP._IOwnership _out193;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
              (this).GenExpr(_1778_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out192, out _out193, out _out194);
              _1795_onExpr = _out192;
              _1796___v96 = _out193;
              _1797_enclosingIdents = _out194;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1797_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1798_renderedName;
              _1798_renderedName = (this).GetMethodName(_1778_on, _1779_name);
              DAST._IExpression _source92 = _1778_on;
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
                    _1795_onExpr = (_1795_onExpr).FSel(_1798_renderedName);
                  }
                }
              }
              if (unmatched92) {
                unmatched92 = false;
                {
                  if (!object.Equals(_1795_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source93 = _1779_name;
                    bool unmatched93 = true;
                    if (unmatched93) {
                      if (_source93.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source93.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1799_tpe = onType0.dtor_value;
                          unmatched93 = false;
                          RAST._IType _1800_typ;
                          RAST._IType _out195;
                          _out195 = (this).GenType(_1799_tpe, DCOMP.GenTypeContext.@default());
                          _1800_typ = _out195;
                          if (((_1800_typ).IsObjectOrPointer()) && (!object.Equals(_1795_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1795_onExpr = ((this).modify__macro).Apply1(_1795_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched93) {
                      unmatched93 = false;
                    }
                  }
                  _1795_onExpr = (_1795_onExpr).Sel(_1798_renderedName);
                }
              }
              generated = ((_1795_onExpr).ApplyType(_1785_typeExprs)).Apply(_1783_argExprs);
            }
            if (((_1782_maybeOutVars).is_Some) && ((new BigInteger(((_1782_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1801_outVar;
              _1801_outVar = DCOMP.__default.escapeVar(((_1782_maybeOutVars).dtor_value).Select(BigInteger.Zero));
              if (!((env).CanReadWithoutClone(_1801_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1801_outVar, generated);
            } else if (((_1782_maybeOutVars).is_None) || ((new BigInteger(((_1782_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1802_tmpVar;
              _1802_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1803_tmpId;
              _1803_tmpId = RAST.Expr.create_Identifier(_1802_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1802_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1804_outVars;
              _1804_outVars = (_1782_maybeOutVars).dtor_value;
              BigInteger _hi36 = new BigInteger((_1804_outVars).Count);
              for (BigInteger _1805_outI = BigInteger.Zero; _1805_outI < _hi36; _1805_outI++) {
                Dafny.ISequence<Dafny.Rune> _1806_outVar;
                _1806_outVar = DCOMP.__default.escapeVar((_1804_outVars).Select(_1805_outI));
                RAST._IExpr _1807_rhs;
                _1807_rhs = (_1803_tmpId).Sel(Std.Strings.__default.OfNat(_1805_outI));
                if (!((env).CanReadWithoutClone(_1806_outVar))) {
                  _1807_rhs = RAST.__default.MaybePlacebo(_1807_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1806_outVar, _1807_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Return) {
          DAST._IExpression _1808_exprDafny = _source89.dtor_expr;
          unmatched89 = false;
          {
            RAST._IExpr _1809_expr;
            DCOMP._IOwnership _1810___v106;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1811_recIdents;
            RAST._IExpr _out196;
            DCOMP._IOwnership _out197;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out198;
            (this).GenExpr(_1808_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out196, out _out197, out _out198);
            _1809_expr = _out196;
            _1810___v106 = _out197;
            _1811_recIdents = _out198;
            readIdents = _1811_recIdents;
            if (isLast) {
              generated = _1809_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1809_expr));
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
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1812_rustIdents = _source94.dtor_value;
              unmatched94 = false;
              Dafny.ISequence<RAST._IExpr> _1813_tupleArgs;
              _1813_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi37 = new BigInteger((_1812_rustIdents).Count);
              for (BigInteger _1814_i = BigInteger.Zero; _1814_i < _hi37; _1814_i++) {
                RAST._IExpr _1815_rIdent;
                DCOMP._IOwnership _1816___v107;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1817___v108;
                RAST._IExpr _out199;
                DCOMP._IOwnership _out200;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
                (this).GenIdent((_1812_rustIdents).Select(_1814_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out199, out _out200, out _out201);
                _1815_rIdent = _out199;
                _1816___v107 = _out200;
                _1817___v108 = _out201;
                _1813_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1813_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1815_rIdent));
              }
              if ((new BigInteger((_1813_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1813_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1813_tupleArgs)));
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
        DAST._IExpression _1818_e = _source89.dtor_Print_a0;
        unmatched89 = false;
        {
          RAST._IExpr _1819_printedExpr;
          DCOMP._IOwnership _1820_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1821_recIdents;
          RAST._IExpr _out202;
          DCOMP._IOwnership _out203;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out204;
          (this).GenExpr(_1818_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out202, out _out203, out _out204);
          _1819_printedExpr = _out202;
          _1820_recOwnership = _out203;
          _1821_recIdents = _out204;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).AsExpr()).Apply1(_1819_printedExpr)));
          readIdents = _1821_recIdents;
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
            bool _1822_b = _h170.dtor_BoolLiteral_a0;
            unmatched96 = false;
            {
              RAST._IExpr _out209;
              DCOMP._IOwnership _out210;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1822_b), expectedOwnership, out _out209, out _out210);
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
            Dafny.ISequence<Dafny.Rune> _1823_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1824_t = _h171.dtor_IntLiteral_a1;
            unmatched96 = false;
            {
              DAST._IType _source97 = _1824_t;
              bool unmatched97 = true;
              if (unmatched97) {
                if (_source97.is_Primitive) {
                  DAST._IPrimitive _h70 = _source97.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched97 = false;
                    {
                      if ((new BigInteger((_1823_i).Count)) <= (new BigInteger(4))) {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralInt(_1823_i));
                      } else {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1823_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched97) {
                DAST._IType _1825_o = _source97;
                unmatched97 = false;
                {
                  RAST._IType _1826_genType;
                  RAST._IType _out211;
                  _out211 = (this).GenType(_1825_o, DCOMP.GenTypeContext.@default());
                  _1826_genType = _out211;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1823_i), _1826_genType);
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
            Dafny.ISequence<Dafny.Rune> _1827_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1828_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1829_t = _h172.dtor_DecLiteral_a2;
            unmatched96 = false;
            {
              DAST._IType _source98 = _1829_t;
              bool unmatched98 = true;
              if (unmatched98) {
                if (_source98.is_Primitive) {
                  DAST._IPrimitive _h71 = _source98.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched98 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1827_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1828_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched98) {
                DAST._IType _1830_o = _source98;
                unmatched98 = false;
                {
                  RAST._IType _1831_genType;
                  RAST._IType _out214;
                  _out214 = (this).GenType(_1830_o, DCOMP.GenTypeContext.@default());
                  _1831_genType = _out214;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1827_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1828_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1831_genType);
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
            Dafny.ISequence<Dafny.Rune> _1832_l = _h173.dtor_StringLiteral_a0;
            bool _1833_verbatim = _h173.dtor_verbatim;
            unmatched96 = false;
            {
              r = (((RAST.__default.dafny__runtime).MSel((this).string__of)).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1832_l, false, _1833_verbatim));
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
            BigInteger _1834_c = _h174.dtor_CharLiteralUTF16_a0;
            unmatched96 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1834_c));
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
            Dafny.Rune _1835_c = _h175.dtor_CharLiteral_a0;
            unmatched96 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1835_c).Value)));
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
        DAST._IType _1836_tpe = _h176.dtor_Null_a0;
        unmatched96 = false;
        {
          RAST._IType _1837_tpeGen;
          RAST._IType _out223;
          _out223 = (this).GenType(_1836_tpe, DCOMP.GenTypeContext.@default());
          _1837_tpeGen = _out223;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null_mut"));
          } else {
            r = RAST.Expr.create_TypeAscription((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1837_tpeGen);
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
      DAST._IBinOp _1838_op = _let_tmp_rhs56.dtor_op;
      DAST._IExpression _1839_lExpr = _let_tmp_rhs56.dtor_left;
      DAST._IExpression _1840_rExpr = _let_tmp_rhs56.dtor_right;
      DAST.Format._IBinaryOpFormat _1841_format = _let_tmp_rhs56.dtor_format2;
      bool _1842_becomesLeftCallsRight;
      _1842_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source99 = _1838_op;
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
      bool _1843_becomesRightCallsLeft;
      _1843_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source100 = _1838_op;
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
      bool _1844_becomesCallLeftRight;
      _1844_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source101 = _1838_op;
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
      DCOMP._IOwnership _1845_expectedLeftOwnership;
      _1845_expectedLeftOwnership = ((_1842_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1843_becomesRightCallsLeft) || (_1844_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1846_expectedRightOwnership;
      _1846_expectedRightOwnership = (((_1842_becomesLeftCallsRight) || (_1844_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1843_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1847_left;
      DCOMP._IOwnership _1848___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1849_recIdentsL;
      RAST._IExpr _out226;
      DCOMP._IOwnership _out227;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
      (this).GenExpr(_1839_lExpr, selfIdent, env, _1845_expectedLeftOwnership, out _out226, out _out227, out _out228);
      _1847_left = _out226;
      _1848___v113 = _out227;
      _1849_recIdentsL = _out228;
      RAST._IExpr _1850_right;
      DCOMP._IOwnership _1851___v114;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1852_recIdentsR;
      RAST._IExpr _out229;
      DCOMP._IOwnership _out230;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out231;
      (this).GenExpr(_1840_rExpr, selfIdent, env, _1846_expectedRightOwnership, out _out229, out _out230, out _out231);
      _1850_right = _out229;
      _1851___v114 = _out230;
      _1852_recIdentsR = _out231;
      DAST._IBinOp _source102 = _1838_op;
      bool unmatched102 = true;
      if (unmatched102) {
        if (_source102.is_In) {
          unmatched102 = false;
          {
            r = ((_1850_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1847_left);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_SeqProperPrefix) {
          unmatched102 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1847_left, _1850_right, _1841_format);
        }
      }
      if (unmatched102) {
        if (_source102.is_SeqPrefix) {
          unmatched102 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1847_left, _1850_right, _1841_format);
        }
      }
      if (unmatched102) {
        if (_source102.is_SetMerge) {
          unmatched102 = false;
          {
            r = ((_1847_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1850_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_SetSubtraction) {
          unmatched102 = false;
          {
            r = ((_1847_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1850_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_SetIntersection) {
          unmatched102 = false;
          {
            r = ((_1847_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1850_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_Subset) {
          unmatched102 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1847_left, _1850_right, _1841_format);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_ProperSubset) {
          unmatched102 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1847_left, _1850_right, _1841_format);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_SetDisjoint) {
          unmatched102 = false;
          {
            r = ((_1847_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1850_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_MapMerge) {
          unmatched102 = false;
          {
            r = ((_1847_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1850_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_MapSubtraction) {
          unmatched102 = false;
          {
            r = ((_1847_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1850_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_MultisetMerge) {
          unmatched102 = false;
          {
            r = ((_1847_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1850_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_MultisetSubtraction) {
          unmatched102 = false;
          {
            r = ((_1847_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1850_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_MultisetIntersection) {
          unmatched102 = false;
          {
            r = ((_1847_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1850_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_Submultiset) {
          unmatched102 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1847_left, _1850_right, _1841_format);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_ProperSubmultiset) {
          unmatched102 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1847_left, _1850_right, _1841_format);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_MultisetDisjoint) {
          unmatched102 = false;
          {
            r = ((_1847_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1850_right);
          }
        }
      }
      if (unmatched102) {
        if (_source102.is_Concat) {
          unmatched102 = false;
          {
            r = ((_1847_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1850_right);
          }
        }
      }
      if (unmatched102) {
        unmatched102 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1838_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1838_op), _1847_left, _1850_right, _1841_format);
          } else {
            DAST._IBinOp _source103 = _1838_op;
            bool unmatched103 = true;
            if (unmatched103) {
              if (_source103.is_Eq) {
                bool _1853_referential = _source103.dtor_referential;
                unmatched103 = false;
                {
                  if (_1853_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1847_left, _1850_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1840_rExpr).is_SeqValue) && ((new BigInteger(((_1840_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1847_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1839_lExpr).is_SeqValue) && ((new BigInteger(((_1839_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1850_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1847_left, _1850_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched103) {
              if (_source103.is_EuclidianDiv) {
                unmatched103 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1847_left, _1850_right));
                }
              }
            }
            if (unmatched103) {
              if (_source103.is_EuclidianMod) {
                unmatched103 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1847_left, _1850_right));
                }
              }
            }
            if (unmatched103) {
              Dafny.ISequence<Dafny.Rune> _1854_op = _source103.dtor_Passthrough_a0;
              unmatched103 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1854_op, _1847_left, _1850_right, _1841_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1849_recIdentsL, _1852_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs57 = e;
      DAST._IExpression _1855_expr = _let_tmp_rhs57.dtor_value;
      DAST._IType _1856_fromTpe = _let_tmp_rhs57.dtor_from;
      DAST._IType _1857_toTpe = _let_tmp_rhs57.dtor_typ;
      DAST._IType _let_tmp_rhs58 = _1857_toTpe;
      DAST._IResolvedType _let_tmp_rhs59 = _let_tmp_rhs58.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1858_path = _let_tmp_rhs59.dtor_path;
      Dafny.ISequence<DAST._IType> _1859_typeArgs = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs60 = _let_tmp_rhs59.dtor_kind;
      DAST._IType _1860_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _1861_range = _let_tmp_rhs60.dtor_range;
      bool _1862_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1863___v116 = _let_tmp_rhs59.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1864___v117 = _let_tmp_rhs59.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1865___v118 = _let_tmp_rhs59.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1866_nativeToType;
      _1866_nativeToType = DCOMP.COMP.NewtypeRangeToRustType(_1861_range);
      if (object.Equals(_1856_fromTpe, _1860_b)) {
        RAST._IExpr _1867_recursiveGen;
        DCOMP._IOwnership _1868_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1869_recIdents;
        RAST._IExpr _out234;
        DCOMP._IOwnership _out235;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out236;
        (this).GenExpr(_1855_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out234, out _out235, out _out236);
        _1867_recursiveGen = _out234;
        _1868_recOwned = _out235;
        _1869_recIdents = _out236;
        readIdents = _1869_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source104 = _1866_nativeToType;
        bool unmatched104 = true;
        if (unmatched104) {
          if (_source104.is_Some) {
            RAST._IType _1870_v = _source104.dtor_value;
            unmatched104 = false;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1867_recursiveGen, RAST.Expr.create_ExprFromType(_1870_v)));
            RAST._IExpr _out237;
            DCOMP._IOwnership _out238;
            (this).FromOwned(r, expectedOwnership, out _out237, out _out238);
            r = _out237;
            resultingOwnership = _out238;
          }
        }
        if (unmatched104) {
          unmatched104 = false;
          if (_1862_erase) {
            r = _1867_recursiveGen;
          } else {
            RAST._IType _1871_rhsType;
            RAST._IType _out239;
            _out239 = (this).GenType(_1857_toTpe, DCOMP.GenTypeContext.@default());
            _1871_rhsType = _out239;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1871_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1867_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out240;
          DCOMP._IOwnership _out241;
          (this).FromOwnership(r, _1868_recOwned, expectedOwnership, out _out240, out _out241);
          r = _out240;
          resultingOwnership = _out241;
        }
      } else {
        if ((_1866_nativeToType).is_Some) {
          DAST._IType _source105 = _1856_fromTpe;
          bool unmatched105 = true;
          if (unmatched105) {
            if (_source105.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source105.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1872_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1873_range0 = kind1.dtor_range;
                bool _1874_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1875_attributes0 = resolved1.dtor_attributes;
                unmatched105 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1876_nativeFromType;
                  _1876_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1873_range0);
                  if ((_1876_nativeFromType).is_Some) {
                    RAST._IExpr _1877_recursiveGen;
                    DCOMP._IOwnership _1878_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1879_recIdents;
                    RAST._IExpr _out242;
                    DCOMP._IOwnership _out243;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out244;
                    (this).GenExpr(_1855_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out242, out _out243, out _out244);
                    _1877_recursiveGen = _out242;
                    _1878_recOwned = _out243;
                    _1879_recIdents = _out244;
                    RAST._IExpr _out245;
                    DCOMP._IOwnership _out246;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1877_recursiveGen, (_1866_nativeToType).dtor_value), _1878_recOwned, expectedOwnership, out _out245, out _out246);
                    r = _out245;
                    resultingOwnership = _out246;
                    readIdents = _1879_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched105) {
            unmatched105 = false;
          }
          if (object.Equals(_1856_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1880_recursiveGen;
            DCOMP._IOwnership _1881_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1882_recIdents;
            RAST._IExpr _out247;
            DCOMP._IOwnership _out248;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
            (this).GenExpr(_1855_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out247, out _out248, out _out249);
            _1880_recursiveGen = _out247;
            _1881_recOwned = _out248;
            _1882_recIdents = _out249;
            RAST._IExpr _out250;
            DCOMP._IOwnership _out251;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1880_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1866_nativeToType).dtor_value), _1881_recOwned, expectedOwnership, out _out250, out _out251);
            r = _out250;
            resultingOwnership = _out251;
            readIdents = _1882_recIdents;
            return ;
          }
        }
        RAST._IExpr _out252;
        DCOMP._IOwnership _out253;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out254;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1855_expr, _1856_fromTpe, _1860_b), _1860_b, _1857_toTpe), selfIdent, env, expectedOwnership, out _out252, out _out253, out _out254);
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
      DAST._IExpression _1883_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _1884_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _1885_toTpe = _let_tmp_rhs61.dtor_typ;
      DAST._IType _let_tmp_rhs62 = _1884_fromTpe;
      DAST._IResolvedType _let_tmp_rhs63 = _let_tmp_rhs62.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1886___v124 = _let_tmp_rhs63.dtor_path;
      Dafny.ISequence<DAST._IType> _1887___v125 = _let_tmp_rhs63.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs64 = _let_tmp_rhs63.dtor_kind;
      DAST._IType _1888_b = _let_tmp_rhs64.dtor_baseType;
      DAST._INewtypeRange _1889_range = _let_tmp_rhs64.dtor_range;
      bool _1890_erase = _let_tmp_rhs64.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1891_attributes = _let_tmp_rhs63.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1892___v126 = _let_tmp_rhs63.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1893___v127 = _let_tmp_rhs63.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1894_nativeFromType;
      _1894_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1889_range);
      if (object.Equals(_1888_b, _1885_toTpe)) {
        RAST._IExpr _1895_recursiveGen;
        DCOMP._IOwnership _1896_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1897_recIdents;
        RAST._IExpr _out255;
        DCOMP._IOwnership _out256;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out257;
        (this).GenExpr(_1883_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out255, out _out256, out _out257);
        _1895_recursiveGen = _out255;
        _1896_recOwned = _out256;
        _1897_recIdents = _out257;
        readIdents = _1897_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source106 = _1894_nativeFromType;
        bool unmatched106 = true;
        if (unmatched106) {
          if (_source106.is_Some) {
            RAST._IType _1898_v = _source106.dtor_value;
            unmatched106 = false;
            RAST._IType _1899_toTpeRust;
            RAST._IType _out258;
            _out258 = (this).GenType(_1885_toTpe, DCOMP.GenTypeContext.@default());
            _1899_toTpeRust = _out258;
            r = ((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1899_toTpeRust))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1895_recursiveGen));
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            (this).FromOwned(r, expectedOwnership, out _out259, out _out260);
            r = _out259;
            resultingOwnership = _out260;
          }
        }
        if (unmatched106) {
          unmatched106 = false;
          if (_1890_erase) {
            r = _1895_recursiveGen;
          } else {
            r = (_1895_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out261;
          DCOMP._IOwnership _out262;
          (this).FromOwnership(r, _1896_recOwned, expectedOwnership, out _out261, out _out262);
          r = _out261;
          resultingOwnership = _out262;
        }
      } else {
        if ((_1894_nativeFromType).is_Some) {
          if (object.Equals(_1885_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1900_recursiveGen;
            DCOMP._IOwnership _1901_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1902_recIdents;
            RAST._IExpr _out263;
            DCOMP._IOwnership _out264;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out265;
            (this).GenExpr(_1883_expr, selfIdent, env, expectedOwnership, out _out263, out _out264, out _out265);
            _1900_recursiveGen = _out263;
            _1901_recOwned = _out264;
            _1902_recIdents = _out265;
            RAST._IExpr _out266;
            DCOMP._IOwnership _out267;
            (this).FromOwnership((((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(RAST.Expr.create_TypeAscription(_1900_recursiveGen, (this).DafnyCharUnderlying)), _1901_recOwned, expectedOwnership, out _out266, out _out267);
            r = _out266;
            resultingOwnership = _out267;
            readIdents = _1902_recIdents;
            return ;
          }
        }
        RAST._IExpr _out268;
        DCOMP._IOwnership _out269;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1883_expr, _1884_fromTpe, _1888_b), _1888_b, _1885_toTpe), selfIdent, env, expectedOwnership, out _out268, out _out269, out _out270);
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
        Std.Wrappers._IResult<__T, __E> _1903_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1903_valueOrError0).IsFailure()) {
          return (_1903_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1904_head = (_1903_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1905_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1905_valueOrError1).IsFailure()) {
            return (_1905_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1906_tail = (_1905_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1904_head), _1906_tail));
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
          RAST._IType _1907_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1908_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel((this).upcast)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1907_fromTpeUnderlying, _1908_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1909_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1909_valueOrError0).IsFailure()) {
          return (_1909_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1910_lambda = (_1909_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1910_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).AsExpr()).Apply1(_1910_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Dafny.ISequence<BigInteger> _1911_indices = ((((fromType).is_UserDefined) && ((((fromType).dtor_resolved).dtor_kind).is_Datatype)) ? (Std.Collections.Seq.__default.Filter<BigInteger>(Dafny.Helpers.Id<Func<RAST._IType, DAST._IType, Func<BigInteger, bool>>>((_1912_fromTpe, _1913_fromType) => ((System.Func<BigInteger, bool>)((_1914_i) => {
          return ((((_1914_i).Sign != -1) && ((_1914_i) < (new BigInteger(((_1912_fromTpe).dtor_arguments).Count)))) ? (!(((_1914_i).Sign != -1) && ((_1914_i) < (new BigInteger(((((_1913_fromType).dtor_resolved).dtor_kind).dtor_variances).Count)))) || (!((((((_1913_fromType).dtor_resolved).dtor_kind).dtor_variances).Select(_1914_i)).is_Nonvariant))) : (false));
        })))(fromTpe, fromType), ((System.Func<Dafny.ISequence<BigInteger>>) (() => {
          BigInteger dim14 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr14 = new BigInteger[Dafny.Helpers.ToIntChecked(dim14, "array size exceeds memory limit")];
          for (int i14 = 0; i14 < dim14; i14++) {
            var _1915_i = (BigInteger) i14;
            arr14[(int)(_1915_i)] = _1915_i;
          }
          return Dafny.Sequence<BigInteger>.FromArray(arr14);
        }))())) : (((System.Func<Dafny.ISequence<BigInteger>>) (() => {
          BigInteger dim15 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr15 = new BigInteger[Dafny.Helpers.ToIntChecked(dim15, "array size exceeds memory limit")];
          for (int i15 = 0; i15 < dim15; i15++) {
            var _1916_i = (BigInteger) i15;
            arr15[(int)(_1916_i)] = _1916_i;
          }
          return Dafny.Sequence<BigInteger>.FromArray(arr15);
        }))()));
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1917_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim16 = new BigInteger((_1911_indices).Count);
          var arr16 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim16, "array size exceeds memory limit")];
          for (int i16 = 0; i16 < dim16; i16++) {
            var _1918_j = (BigInteger) i16;
            arr16[(int)(_1918_j)] = Dafny.Helpers.Let<BigInteger, Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>((_1911_indices).Select(_1918_j), _pat_let28_0 => Dafny.Helpers.Let<BigInteger, Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>(_pat_let28_0, _1919_i => (this).UpcastConversionLambda((((_pat_let_tv194).dtor_resolved).dtor_typeArgs).Select(_1919_i), ((_pat_let_tv195).dtor_arguments).Select(_1919_i), (((_pat_let_tv196).dtor_resolved).dtor_typeArgs).Select(_1919_i), ((_pat_let_tv197).dtor_arguments).Select(_1919_i), _pat_let_tv198)));
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr16);
        }))());
        if ((_1917_valueOrError1).IsFailure()) {
          return (_1917_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1920_lambdas = (_1917_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim17 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr17 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim17, "array size exceeds memory limit")];
  for (int i17 = 0; i17 < dim17; i17++) {
    var _1921_i = (BigInteger) i17;
    arr17[(int)(_1921_i)] = ((fromTpe).dtor_arguments).Select(_1921_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr17);
}))())).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1920_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1922_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1923_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1924_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1925_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1926_valueOrError2 = (this).UpcastConversionLambda(_1924_newFromType, _1922_newFromTpe, _1925_newToType, _1923_newToTpe, typeParams);
        if ((_1926_valueOrError2).IsFailure()) {
          return (_1926_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1927_coerceArg = (_1926_valueOrError2).Extract();
          RAST._IPath _1928_collectionType = (RAST.__default.dafny__runtime).MSel(((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name);
          RAST._IExpr _1929_baseType = (((((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? (((_1928_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((((fromTpe).Expand()).dtor_arguments).Select(BigInteger.Zero), _1922_newFromTpe))) : (((_1928_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1922_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1929_baseType).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1927_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1930_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1930_valueOrError3).IsFailure()) {
          return (_1930_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1931_lambda = (_1930_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1931_lambda));
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
      DAST._IExpression _1932_expr = _let_tmp_rhs65.dtor_value;
      DAST._IType _1933_fromTpe = _let_tmp_rhs65.dtor_from;
      DAST._IType _1934_toTpe = _let_tmp_rhs65.dtor_typ;
      RAST._IType _1935_fromTpeGen;
      RAST._IType _out271;
      _out271 = (this).GenType(_1933_fromTpe, DCOMP.GenTypeContext.@default());
      _1935_fromTpeGen = _out271;
      RAST._IType _1936_toTpeGen;
      RAST._IType _out272;
      _out272 = (this).GenType(_1934_toTpe, DCOMP.GenTypeContext.@default());
      _1936_toTpeGen = _out272;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1937_upcastConverter;
      _1937_upcastConverter = (this).UpcastConversionLambda(_1933_fromTpe, _1935_fromTpeGen, _1934_toTpe, _1936_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1937_upcastConverter).is_Success) {
        RAST._IExpr _1938_conversionLambda;
        _1938_conversionLambda = (_1937_upcastConverter).dtor_value;
        RAST._IExpr _1939_recursiveGen;
        DCOMP._IOwnership _1940_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1941_recIdents;
        RAST._IExpr _out273;
        DCOMP._IOwnership _out274;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out275;
        (this).GenExpr(_1932_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out273, out _out274, out _out275);
        _1939_recursiveGen = _out273;
        _1940_recOwned = _out274;
        _1941_recIdents = _out275;
        readIdents = _1941_recIdents;
        r = (_1938_conversionLambda).Apply1(_1939_recursiveGen);
        RAST._IExpr _out276;
        DCOMP._IOwnership _out277;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out276, out _out277);
        r = _out276;
        resultingOwnership = _out277;
      } else if ((this).IsDowncastConversion(_1935_fromTpeGen, _1936_toTpeGen)) {
        RAST._IExpr _1942_recursiveGen;
        DCOMP._IOwnership _1943_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1944_recIdents;
        RAST._IExpr _out278;
        DCOMP._IOwnership _out279;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out280;
        (this).GenExpr(_1932_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out278, out _out279, out _out280);
        _1942_recursiveGen = _out278;
        _1943_recOwned = _out279;
        _1944_recIdents = _out280;
        readIdents = _1944_recIdents;
        _1936_toTpeGen = (_1936_toTpeGen).ObjectOrPointerUnderlying();
        r = (((RAST.__default.dafny__runtime).MSel((this).downcast)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1942_recursiveGen, RAST.Expr.create_ExprFromType(_1936_toTpeGen)));
        RAST._IExpr _out281;
        DCOMP._IOwnership _out282;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out281, out _out282);
        r = _out281;
        resultingOwnership = _out282;
      } else {
        RAST._IExpr _1945_recursiveGen;
        DCOMP._IOwnership _1946_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1947_recIdents;
        RAST._IExpr _out283;
        DCOMP._IOwnership _out284;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out285;
        (this).GenExpr(_1932_expr, selfIdent, env, expectedOwnership, out _out283, out _out284, out _out285);
        _1945_recursiveGen = _out283;
        _1946_recOwned = _out284;
        _1947_recIdents = _out285;
        readIdents = _1947_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs66 = _1937_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs67 = _let_tmp_rhs66.dtor_error;
        DAST._IType _1948_fromType = _let_tmp_rhs67.dtor__0;
        RAST._IType _1949_fromTpeGen = _let_tmp_rhs67.dtor__1;
        DAST._IType _1950_toType = _let_tmp_rhs67.dtor__2;
        RAST._IType _1951_toTpeGen = _let_tmp_rhs67.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1952_m = _let_tmp_rhs67.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1953_msg;
        _1953_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1949_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1951_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1953_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1945_recursiveGen)._ToString(DCOMP.__default.IND), _1953_msg));
        RAST._IExpr _out286;
        DCOMP._IOwnership _out287;
        (this).FromOwnership(r, _1946_recOwned, expectedOwnership, out _out286, out _out287);
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
      DAST._IExpression _1954_expr = _let_tmp_rhs68.dtor_value;
      DAST._IType _1955_fromTpe = _let_tmp_rhs68.dtor_from;
      DAST._IType _1956_toTpe = _let_tmp_rhs68.dtor_typ;
      if (object.Equals(_1955_fromTpe, _1956_toTpe)) {
        RAST._IExpr _1957_recursiveGen;
        DCOMP._IOwnership _1958_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1959_recIdents;
        RAST._IExpr _out288;
        DCOMP._IOwnership _out289;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
        (this).GenExpr(_1954_expr, selfIdent, env, expectedOwnership, out _out288, out _out289, out _out290);
        _1957_recursiveGen = _out288;
        _1958_recOwned = _out289;
        _1959_recIdents = _out290;
        r = _1957_recursiveGen;
        RAST._IExpr _out291;
        DCOMP._IOwnership _out292;
        (this).FromOwnership(r, _1958_recOwned, expectedOwnership, out _out291, out _out292);
        r = _out291;
        resultingOwnership = _out292;
        readIdents = _1959_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source107 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1955_fromTpe, _1956_toTpe);
        bool unmatched107 = true;
        if (unmatched107) {
          DAST._IType _10 = _source107.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1960_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1961_range = kind2.dtor_range;
              bool _1962_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1963_attributes = resolved2.dtor_attributes;
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
              DAST._IType _1964_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1965_range = kind3.dtor_range;
              bool _1966_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1967_attributes = resolved3.dtor_attributes;
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
                    RAST._IExpr _1968_recursiveGen;
                    DCOMP._IOwnership _1969___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1970_recIdents;
                    RAST._IExpr _out299;
                    DCOMP._IOwnership _out300;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out301;
                    (this).GenExpr(_1954_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out299, out _out300, out _out301);
                    _1968_recursiveGen = _out299;
                    _1969___v138 = _out300;
                    _1970_recIdents = _out301;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1968_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out302;
                    DCOMP._IOwnership _out303;
                    (this).FromOwned(r, expectedOwnership, out _out302, out _out303);
                    r = _out302;
                    resultingOwnership = _out303;
                    readIdents = _1970_recIdents;
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
                    RAST._IExpr _1971_recursiveGen;
                    DCOMP._IOwnership _1972___v139;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1973_recIdents;
                    RAST._IExpr _out304;
                    DCOMP._IOwnership _out305;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out306;
                    (this).GenExpr(_1954_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out304, out _out305, out _out306);
                    _1971_recursiveGen = _out304;
                    _1972___v139 = _out305;
                    _1973_recIdents = _out306;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1971_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out307;
                    DCOMP._IOwnership _out308;
                    (this).FromOwned(r, expectedOwnership, out _out307, out _out308);
                    r = _out307;
                    resultingOwnership = _out308;
                    readIdents = _1973_recIdents;
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
                  RAST._IType _1974_rhsType;
                  RAST._IType _out309;
                  _out309 = (this).GenType(_1956_toTpe, DCOMP.GenTypeContext.@default());
                  _1974_rhsType = _out309;
                  RAST._IExpr _1975_recursiveGen;
                  DCOMP._IOwnership _1976___v141;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1977_recIdents;
                  RAST._IExpr _out310;
                  DCOMP._IOwnership _out311;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out312;
                  (this).GenExpr(_1954_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out310, out _out311, out _out312);
                  _1975_recursiveGen = _out310;
                  _1976___v141 = _out311;
                  _1977_recIdents = _out312;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1974_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1975_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out313;
                  DCOMP._IOwnership _out314;
                  (this).FromOwned(r, expectedOwnership, out _out313, out _out314);
                  r = _out313;
                  resultingOwnership = _out314;
                  readIdents = _1977_recIdents;
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
                  RAST._IType _1978_rhsType;
                  RAST._IType _out315;
                  _out315 = (this).GenType(_1955_fromTpe, DCOMP.GenTypeContext.@default());
                  _1978_rhsType = _out315;
                  RAST._IExpr _1979_recursiveGen;
                  DCOMP._IOwnership _1980___v143;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1981_recIdents;
                  RAST._IExpr _out316;
                  DCOMP._IOwnership _out317;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out318;
                  (this).GenExpr(_1954_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out316, out _out317, out _out318);
                  _1979_recursiveGen = _out316;
                  _1980___v143 = _out317;
                  _1981_recIdents = _out318;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1979_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out319;
                  DCOMP._IOwnership _out320;
                  (this).FromOwned(r, expectedOwnership, out _out319, out _out320);
                  r = _out319;
                  resultingOwnership = _out320;
                  readIdents = _1981_recIdents;
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
                    RAST._IType _1982_rhsType;
                    RAST._IType _out321;
                    _out321 = (this).GenType(_1956_toTpe, DCOMP.GenTypeContext.@default());
                    _1982_rhsType = _out321;
                    RAST._IExpr _1983_recursiveGen;
                    DCOMP._IOwnership _1984___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1985_recIdents;
                    RAST._IExpr _out322;
                    DCOMP._IOwnership _out323;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out324;
                    (this).GenExpr(_1954_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out322, out _out323, out _out324);
                    _1983_recursiveGen = _out322;
                    _1984___v144 = _out323;
                    _1985_recIdents = _out324;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1983_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out325;
                    DCOMP._IOwnership _out326;
                    (this).FromOwned(r, expectedOwnership, out _out325, out _out326);
                    r = _out325;
                    resultingOwnership = _out326;
                    readIdents = _1985_recIdents;
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
                    RAST._IType _1986_rhsType;
                    RAST._IType _out327;
                    _out327 = (this).GenType(_1955_fromTpe, DCOMP.GenTypeContext.@default());
                    _1986_rhsType = _out327;
                    RAST._IExpr _1987_recursiveGen;
                    DCOMP._IOwnership _1988___v145;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1989_recIdents;
                    RAST._IExpr _out328;
                    DCOMP._IOwnership _out329;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out330;
                    (this).GenExpr(_1954_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out328, out _out329, out _out330);
                    _1987_recursiveGen = _out328;
                    _1988___v145 = _out329;
                    _1989_recIdents = _out330;
                    r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1((_1987_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out331;
                    DCOMP._IOwnership _out332;
                    (this).FromOwned(r, expectedOwnership, out _out331, out _out332);
                    r = _out331;
                    resultingOwnership = _out332;
                    readIdents = _1989_recIdents;
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
                RAST._IExpr _1990_recursiveGen;
                DCOMP._IOwnership _1991___v148;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1992_recIdents;
                RAST._IExpr _out333;
                DCOMP._IOwnership _out334;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out335;
                (this).GenExpr(_1954_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out333, out _out334, out _out335);
                _1990_recursiveGen = _out333;
                _1991___v148 = _out334;
                _1992_recIdents = _out335;
                RAST._IType _1993_toTpeGen;
                RAST._IType _out336;
                _out336 = (this).GenType(_1956_toTpe, DCOMP.GenTypeContext.@default());
                _1993_toTpeGen = _out336;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1990_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1993_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out337;
                DCOMP._IOwnership _out338;
                (this).FromOwned(r, expectedOwnership, out _out337, out _out338);
                r = _out337;
                resultingOwnership = _out338;
                readIdents = _1992_recIdents;
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
      Std.Wrappers._IOption<RAST._IType> _1994_tpe;
      _1994_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1995_placeboOpt;
      _1995_placeboOpt = (((_1994_tpe).is_Some) ? (((_1994_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1996_currentlyBorrowed;
      _1996_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1997_noNeedOfClone;
      _1997_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1995_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1996_currentlyBorrowed = false;
        _1997_noNeedOfClone = true;
        _1994_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1995_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_1996_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1994_tpe).is_Some) && (((_1994_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1998_needObjectFromRef;
        _1998_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source108 = (selfIdent).dtor_dafnyType;
          bool unmatched108 = true;
          if (unmatched108) {
            if (_source108.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source108.dtor_resolved;
              DAST._IResolvedTypeBase _1999_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _2000_attributes = resolved4.dtor_attributes;
              unmatched108 = false;
              return ((_1999_base).is_Class) || ((_1999_base).is_Trait);
            }
          }
          if (unmatched108) {
            unmatched108 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_1998_needObjectFromRef) {
          r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1997_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1997_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1996_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1994_tpe).is_Some) && (((_1994_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_2001_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_2001_attributes).UniqueElements, false, (((_exists_var_2) => {
        DAST._IAttribute _2002_attribute = (DAST._IAttribute)_exists_var_2;
        return ((_2001_attributes).Contains(_2002_attribute)) && ((((_2002_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_2002_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      Dafny.ISequence<DAST._IFormal> _2003_signature;
      _2003_signature = (((name).is_CallName) ? ((((((name).dtor_receiverArg).is_Some) && ((name).dtor_receiverAsArgument)) ? (Dafny.Sequence<DAST._IFormal>.Concat(Dafny.Sequence<DAST._IFormal>.FromElements(((name).dtor_receiverArg).dtor_value), ((name).dtor_signature))) : (((name).dtor_signature)))) : (Dafny.Sequence<DAST._IFormal>.FromElements()));
      BigInteger _hi38 = new BigInteger((args).Count);
      for (BigInteger _2004_i = BigInteger.Zero; _2004_i < _hi38; _2004_i++) {
        DCOMP._IOwnership _2005_argOwnership;
        _2005_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if ((_2004_i) < (new BigInteger((_2003_signature).Count))) {
          RAST._IType _2006_tpe;
          RAST._IType _out342;
          _out342 = (this).GenType(((_2003_signature).Select(_2004_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _2006_tpe = _out342;
          if ((_2006_tpe).CanReadWithoutClone()) {
            _2005_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _2007_argExpr;
        DCOMP._IOwnership _2008___v155;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2009_argIdents;
        RAST._IExpr _out343;
        DCOMP._IOwnership _out344;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out345;
        (this).GenExpr((args).Select(_2004_i), selfIdent, env, _2005_argOwnership, out _out343, out _out344, out _out345);
        _2007_argExpr = _out343;
        _2008___v155 = _out344;
        _2009_argIdents = _out345;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2007_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2009_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi39 = new BigInteger((typeArgs).Count);
      for (BigInteger _2010_typeI = BigInteger.Zero; _2010_typeI < _hi39; _2010_typeI++) {
        RAST._IType _2011_typeExpr;
        RAST._IType _out346;
        _out346 = (this).GenType((typeArgs).Select(_2010_typeI), DCOMP.GenTypeContext.@default());
        _2011_typeExpr = _out346;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2011_typeExpr));
      }
      DAST._ICallName _source109 = name;
      bool unmatched109 = true;
      if (unmatched109) {
        if (_source109.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _2012_nameIdent = _source109.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType1 = _source109.dtor_onType;
          if (onType1.is_Some) {
            DAST._IType value10 = onType1.dtor_value;
            if (value10.is_UserDefined) {
              DAST._IResolvedType _2013_resolvedType = value10.dtor_resolved;
              unmatched109 = false;
              if ((((_2013_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_2014_resolvedType, _2015_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.SingleValue<Dafny.ISequence<Dafny.Rune>>(_2015_nameIdent), true, (((_forall_var_8) => {
                Dafny.ISequence<Dafny.Rune> _2016_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                return !(((_2014_resolvedType).dtor_properMethods).Contains(_2016_m)) || (!object.Equals(_2016_m, _2015_nameIdent));
              }))))(_2013_resolvedType, _2012_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_2013_resolvedType, (_2012_nameIdent)), _2013_resolvedType));
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
          Dafny.ISequence<Dafny.Rune> _2017_ident = _source110.dtor_name;
          unmatched110 = false;
          if ((_pat_let_tv199).is_ExternCompanion) {
            return (_2017_ident);
          } else {
            return DCOMP.__default.escapeName(_2017_ident);
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
          Dafny.ISequence<Dafny.Rune> _2018_name = _source111.dtor_name;
          unmatched111 = false;
          {
            RAST._IExpr _out350;
            DCOMP._IOwnership _out351;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out352;
            (this).GenIdent(DCOMP.__default.escapeVar(_2018_name), selfIdent, env, expectedOwnership, out _out350, out _out351, out _out352);
            r = _out350;
            resultingOwnership = _out351;
            readIdents = _out352;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_ExternCompanion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2019_path = _source111.dtor_ExternCompanion_a0;
          unmatched111 = false;
          {
            RAST._IExpr _out353;
            _out353 = DCOMP.COMP.GenPathExpr(_2019_path, false);
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
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2020_path = _source111.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _2021_typeArgs = _source111.dtor_typeArgs;
          unmatched111 = false;
          {
            RAST._IExpr _out356;
            _out356 = DCOMP.COMP.GenPathExpr(_2020_path, true);
            r = _out356;
            if ((new BigInteger((_2021_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _2022_typeExprs;
              _2022_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_2021_typeArgs).Count);
              for (BigInteger _2023_i = BigInteger.Zero; _2023_i < _hi40; _2023_i++) {
                RAST._IType _2024_typeExpr;
                RAST._IType _out357;
                _out357 = (this).GenType((_2021_typeArgs).Select(_2023_i), DCOMP.GenTypeContext.@default());
                _2024_typeExpr = _out357;
                _2022_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_2022_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2024_typeExpr));
              }
              r = (r).ApplyType(_2022_typeExprs);
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
          DAST._IType _2025_typ = _source111.dtor_typ;
          unmatched111 = false;
          {
            RAST._IType _2026_typExpr;
            RAST._IType _out360;
            _out360 = (this).GenType(_2025_typ, DCOMP.GenTypeContext.@default());
            _2026_typExpr = _out360;
            if ((_2026_typExpr).IsObjectOrPointer()) {
              r = (_2026_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_2026_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
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
          Dafny.ISequence<DAST._IExpression> _2027_values = _source111.dtor_Tuple_a0;
          unmatched111 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2028_exprs;
            _2028_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi41 = new BigInteger((_2027_values).Count);
            for (BigInteger _2029_i = BigInteger.Zero; _2029_i < _hi41; _2029_i++) {
              RAST._IExpr _2030_recursiveGen;
              DCOMP._IOwnership _2031___v165;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2032_recIdents;
              RAST._IExpr _out363;
              DCOMP._IOwnership _out364;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out365;
              (this).GenExpr((_2027_values).Select(_2029_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out363, out _out364, out _out365);
              _2030_recursiveGen = _out363;
              _2031___v165 = _out364;
              _2032_recIdents = _out365;
              _2028_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_2028_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2030_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2032_recIdents);
            }
            r = (((new BigInteger((_2027_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_2028_exprs)) : (RAST.__default.SystemTuple(_2028_exprs)));
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
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2033_path = _source111.dtor_path;
          Dafny.ISequence<DAST._IType> _2034_typeArgs = _source111.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2035_args = _source111.dtor_args;
          unmatched111 = false;
          {
            RAST._IExpr _out368;
            _out368 = DCOMP.COMP.GenPathExpr(_2033_path, true);
            r = _out368;
            if ((new BigInteger((_2034_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _2036_typeExprs;
              _2036_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi42 = new BigInteger((_2034_typeArgs).Count);
              for (BigInteger _2037_i = BigInteger.Zero; _2037_i < _hi42; _2037_i++) {
                RAST._IType _2038_typeExpr;
                RAST._IType _out369;
                _out369 = (this).GenType((_2034_typeArgs).Select(_2037_i), DCOMP.GenTypeContext.@default());
                _2038_typeExpr = _out369;
                _2036_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_2036_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2038_typeExpr));
              }
              r = (r).ApplyType(_2036_typeExprs);
            }
            r = (r).FSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _2039_arguments;
            _2039_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi43 = new BigInteger((_2035_args).Count);
            for (BigInteger _2040_i = BigInteger.Zero; _2040_i < _hi43; _2040_i++) {
              RAST._IExpr _2041_recursiveGen;
              DCOMP._IOwnership _2042___v166;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2043_recIdents;
              RAST._IExpr _out370;
              DCOMP._IOwnership _out371;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out372;
              (this).GenExpr((_2035_args).Select(_2040_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out370, out _out371, out _out372);
              _2041_recursiveGen = _out370;
              _2042___v166 = _out371;
              _2043_recIdents = _out372;
              _2039_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2039_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2041_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2043_recIdents);
            }
            r = (r).Apply(_2039_arguments);
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
          Dafny.ISequence<DAST._IExpression> _2044_dims = _source111.dtor_dims;
          DAST._IType _2045_typ = _source111.dtor_typ;
          unmatched111 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_2044_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _2046_msg;
              _2046_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2046_msg);
              }
              r = RAST.Expr.create_RawExpr(_2046_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _2047_typeGen;
              RAST._IType _out375;
              _out375 = (this).GenType(_2045_typ, DCOMP.GenTypeContext.@default());
              _2047_typeGen = _out375;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _2048_dimExprs;
              _2048_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi44 = new BigInteger((_2044_dims).Count);
              for (BigInteger _2049_i = BigInteger.Zero; _2049_i < _hi44; _2049_i++) {
                RAST._IExpr _2050_recursiveGen;
                DCOMP._IOwnership _2051___v167;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2052_recIdents;
                RAST._IExpr _out376;
                DCOMP._IOwnership _out377;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out378;
                (this).GenExpr((_2044_dims).Select(_2049_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out376, out _out377, out _out378);
                _2050_recursiveGen = _out376;
                _2051___v167 = _out377;
                _2052_recIdents = _out378;
                _2048_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_2048_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_2050_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2052_recIdents);
              }
              if ((new BigInteger((_2044_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _2053_class__name;
                _2053_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_2044_dims).Count)));
                r = (((((RAST.__default.dafny__runtime).MSel(_2053_class__name)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2047_typeGen))).FSel((this).placebos__usize)).Apply(_2048_dimExprs);
              } else {
                r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2047_typeGen))).Apply(_2048_dimExprs);
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
          DAST._IExpression _2054_underlying = _source111.dtor_value;
          unmatched111 = false;
          {
            RAST._IExpr _2055_recursiveGen;
            DCOMP._IOwnership _2056___v168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2057_recIdents;
            RAST._IExpr _out381;
            DCOMP._IOwnership _out382;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
            (this).GenExpr(_2054_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out381, out _out382, out _out383);
            _2055_recursiveGen = _out381;
            _2056___v168 = _out382;
            _2057_recIdents = _out383;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(_2055_recursiveGen);
            readIdents = _2057_recIdents;
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
          DAST._IExpression _2058_underlying = _source111.dtor_value;
          DAST._IType _2059_typ = _source111.dtor_typ;
          unmatched111 = false;
          {
            RAST._IType _2060_tpe;
            RAST._IType _out386;
            _out386 = (this).GenType(_2059_typ, DCOMP.GenTypeContext.@default());
            _2060_tpe = _out386;
            RAST._IExpr _2061_recursiveGen;
            DCOMP._IOwnership _2062___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2063_recIdents;
            RAST._IExpr _out387;
            DCOMP._IOwnership _out388;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
            (this).GenExpr(_2058_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out387, out _out388, out _out389);
            _2061_recursiveGen = _out387;
            _2062___v169 = _out388;
            _2063_recIdents = _out389;
            readIdents = _2063_recIdents;
            if ((_2060_tpe).IsObjectOrPointer()) {
              RAST._IType _2064_t;
              _2064_t = (_2060_tpe).ObjectOrPointerUnderlying();
              if ((_2064_t).is_Array) {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).array__construct)).Apply1(_2061_recursiveGen);
              } else if ((_2064_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _2065_c;
                _2065_c = (_2064_t).MultiArrayClass();
                r = ((((RAST.__default.dafny__runtime).MSel(_2065_c)).AsExpr()).FSel((this).array__construct)).Apply1(_2061_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_2060_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_2060_tpe)._ToString(DCOMP.__default.IND)));
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
          DAST._IResolvedType _2066_datatypeType = _source111.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _2067_typeArgs = _source111.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _2068_variant = _source111.dtor_variant;
          bool _2069_isCo = _source111.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2070_values = _source111.dtor_contents;
          unmatched111 = false;
          {
            RAST._IExpr _out392;
            _out392 = DCOMP.COMP.GenPathExpr((_2066_datatypeType).dtor_path, true);
            r = _out392;
            Dafny.ISequence<RAST._IType> _2071_genTypeArgs;
            _2071_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi45 = new BigInteger((_2067_typeArgs).Count);
            for (BigInteger _2072_i = BigInteger.Zero; _2072_i < _hi45; _2072_i++) {
              RAST._IType _2073_typeExpr;
              RAST._IType _out393;
              _out393 = (this).GenType((_2067_typeArgs).Select(_2072_i), DCOMP.GenTypeContext.@default());
              _2073_typeExpr = _out393;
              _2071_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_2071_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_2073_typeExpr));
            }
            if ((new BigInteger((_2067_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_2071_genTypeArgs);
            }
            r = (r).FSel(DCOMP.__default.escapeName(_2068_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _2074_assignments;
            _2074_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi46 = new BigInteger((_2070_values).Count);
            for (BigInteger _2075_i = BigInteger.Zero; _2075_i < _hi46; _2075_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs69 = (_2070_values).Select(_2075_i);
              Dafny.ISequence<Dafny.Rune> _2076_name = _let_tmp_rhs69.dtor__0;
              DAST._IExpression _2077_value = _let_tmp_rhs69.dtor__1;
              if (_2069_isCo) {
                RAST._IExpr _2078_recursiveGen;
                DCOMP._IOwnership _2079___v170;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2080_recIdents;
                RAST._IExpr _out394;
                DCOMP._IOwnership _out395;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out396;
                (this).GenExpr(_2077_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out394, out _out395, out _out396);
                _2078_recursiveGen = _out394;
                _2079___v170 = _out395;
                _2080_recIdents = _out396;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2080_recIdents);
                Dafny.ISequence<Dafny.Rune> _2081_allReadCloned;
                _2081_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_2080_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _2082_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2080_recIdents).Elements) {
                    _2082_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                    if ((_2080_recIdents).Contains(_2082_next)) {
                      goto after__ASSIGN_SUCH_THAT_3;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4740)");
                after__ASSIGN_SUCH_THAT_3: ;
                  _2081_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2081_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _2082_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2082_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _2080_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2080_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2082_next));
                }
                Dafny.ISequence<Dafny.Rune> _2083_wasAssigned;
                _2083_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _2081_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_2078_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _2074_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2074_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_2076_name), RAST.Expr.create_RawExpr(_2083_wasAssigned))));
              } else {
                RAST._IExpr _2084_recursiveGen;
                DCOMP._IOwnership _2085___v171;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2086_recIdents;
                RAST._IExpr _out397;
                DCOMP._IOwnership _out398;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
                (this).GenExpr(_2077_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out397, out _out398, out _out399);
                _2084_recursiveGen = _out397;
                _2085___v171 = _out398;
                _2086_recIdents = _out399;
                _2074_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2074_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_2076_name), _2084_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2086_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _2074_assignments);
            if ((this).IsRcWrapped((_2066_datatypeType).dtor_attributes)) {
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
          DAST._IExpression _2087_length = _source111.dtor_length;
          DAST._IExpression _2088_expr = _source111.dtor_elem;
          unmatched111 = false;
          {
            RAST._IExpr _2089_recursiveGen;
            DCOMP._IOwnership _2090___v175;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2091_recIdents;
            RAST._IExpr _out405;
            DCOMP._IOwnership _out406;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out407;
            (this).GenExpr(_2088_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out405, out _out406, out _out407);
            _2089_recursiveGen = _out405;
            _2090___v175 = _out406;
            _2091_recIdents = _out407;
            RAST._IExpr _2092_lengthGen;
            DCOMP._IOwnership _2093___v176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2094_lengthIdents;
            RAST._IExpr _out408;
            DCOMP._IOwnership _out409;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out410;
            (this).GenExpr(_2087_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out408, out _out409, out _out410);
            _2092_lengthGen = _out408;
            _2093___v176 = _out409;
            _2094_lengthIdents = _out410;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_2089_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_2092_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2091_recIdents, _2094_lengthIdents);
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
          Dafny.ISequence<DAST._IExpression> _2095_exprs = _source111.dtor_elements;
          DAST._IType _2096_typ = _source111.dtor_typ;
          unmatched111 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _2097_genTpe;
            RAST._IType _out413;
            _out413 = (this).GenType(_2096_typ, DCOMP.GenTypeContext.@default());
            _2097_genTpe = _out413;
            BigInteger _2098_i;
            _2098_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2099_args;
            _2099_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2098_i) < (new BigInteger((_2095_exprs).Count))) {
              RAST._IExpr _2100_recursiveGen;
              DCOMP._IOwnership _2101___v177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2102_recIdents;
              RAST._IExpr _out414;
              DCOMP._IOwnership _out415;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out416;
              (this).GenExpr((_2095_exprs).Select(_2098_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out414, out _out415, out _out416);
              _2100_recursiveGen = _out414;
              _2101___v177 = _out415;
              _2102_recIdents = _out416;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2102_recIdents);
              _2099_args = Dafny.Sequence<RAST._IExpr>.Concat(_2099_args, Dafny.Sequence<RAST._IExpr>.FromElements(_2100_recursiveGen));
              _2098_i = (_2098_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).AsExpr()).Apply(_2099_args);
            if ((new BigInteger((_2099_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType()).Apply1(_2097_genTpe));
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
          Dafny.ISequence<DAST._IExpression> _2103_exprs = _source111.dtor_elements;
          unmatched111 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2104_generatedValues;
            _2104_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2105_i;
            _2105_i = BigInteger.Zero;
            while ((_2105_i) < (new BigInteger((_2103_exprs).Count))) {
              RAST._IExpr _2106_recursiveGen;
              DCOMP._IOwnership _2107___v178;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2108_recIdents;
              RAST._IExpr _out419;
              DCOMP._IOwnership _out420;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out421;
              (this).GenExpr((_2103_exprs).Select(_2105_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out419, out _out420, out _out421);
              _2106_recursiveGen = _out419;
              _2107___v178 = _out420;
              _2108_recIdents = _out421;
              _2104_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2104_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2106_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2108_recIdents);
              _2105_i = (_2105_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).AsExpr()).Apply(_2104_generatedValues);
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
          Dafny.ISequence<DAST._IExpression> _2109_exprs = _source111.dtor_elements;
          unmatched111 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2110_generatedValues;
            _2110_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2111_i;
            _2111_i = BigInteger.Zero;
            while ((_2111_i) < (new BigInteger((_2109_exprs).Count))) {
              RAST._IExpr _2112_recursiveGen;
              DCOMP._IOwnership _2113___v179;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2114_recIdents;
              RAST._IExpr _out424;
              DCOMP._IOwnership _out425;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out426;
              (this).GenExpr((_2109_exprs).Select(_2111_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out424, out _out425, out _out426);
              _2112_recursiveGen = _out424;
              _2113___v179 = _out425;
              _2114_recIdents = _out426;
              _2110_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2110_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2112_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2114_recIdents);
              _2111_i = (_2111_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).AsExpr()).Apply(_2110_generatedValues);
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
          DAST._IExpression _2115_expr = _source111.dtor_ToMultiset_a0;
          unmatched111 = false;
          {
            RAST._IExpr _2116_recursiveGen;
            DCOMP._IOwnership _2117___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2118_recIdents;
            RAST._IExpr _out429;
            DCOMP._IOwnership _out430;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out431;
            (this).GenExpr(_2115_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out429, out _out430, out _out431);
            _2116_recursiveGen = _out429;
            _2117___v180 = _out430;
            _2118_recIdents = _out431;
            r = ((_2116_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2118_recIdents;
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
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2119_mapElems = _source111.dtor_mapElems;
          unmatched111 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _2120_generatedValues;
            _2120_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2121_i;
            _2121_i = BigInteger.Zero;
            while ((_2121_i) < (new BigInteger((_2119_mapElems).Count))) {
              RAST._IExpr _2122_recursiveGenKey;
              DCOMP._IOwnership _2123___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2124_recIdentsKey;
              RAST._IExpr _out434;
              DCOMP._IOwnership _out435;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
              (this).GenExpr(((_2119_mapElems).Select(_2121_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out434, out _out435, out _out436);
              _2122_recursiveGenKey = _out434;
              _2123___v181 = _out435;
              _2124_recIdentsKey = _out436;
              RAST._IExpr _2125_recursiveGenValue;
              DCOMP._IOwnership _2126___v182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2127_recIdentsValue;
              RAST._IExpr _out437;
              DCOMP._IOwnership _out438;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
              (this).GenExpr(((_2119_mapElems).Select(_2121_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out437, out _out438, out _out439);
              _2125_recursiveGenValue = _out437;
              _2126___v182 = _out438;
              _2127_recIdentsValue = _out439;
              _2120_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_2120_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_2122_recursiveGenKey, _2125_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2124_recIdentsKey), _2127_recIdentsValue);
              _2121_i = (_2121_i) + (BigInteger.One);
            }
            _2121_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2128_arguments;
            _2128_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2121_i) < (new BigInteger((_2120_generatedValues).Count))) {
              RAST._IExpr _2129_genKey;
              _2129_genKey = ((_2120_generatedValues).Select(_2121_i)).dtor__0;
              RAST._IExpr _2130_genValue;
              _2130_genValue = ((_2120_generatedValues).Select(_2121_i)).dtor__1;
              _2128_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2128_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _2129_genKey, _2130_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _2121_i = (_2121_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).AsExpr()).Apply(_2128_arguments);
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
          DAST._IExpression _2131_expr = _source111.dtor_expr;
          DAST._IExpression _2132_index = _source111.dtor_indexExpr;
          DAST._IExpression _2133_value = _source111.dtor_value;
          unmatched111 = false;
          {
            RAST._IExpr _2134_exprR;
            DCOMP._IOwnership _2135___v183;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2136_exprIdents;
            RAST._IExpr _out442;
            DCOMP._IOwnership _out443;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out444;
            (this).GenExpr(_2131_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out442, out _out443, out _out444);
            _2134_exprR = _out442;
            _2135___v183 = _out443;
            _2136_exprIdents = _out444;
            RAST._IExpr _2137_indexR;
            DCOMP._IOwnership _2138_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2139_indexIdents;
            RAST._IExpr _out445;
            DCOMP._IOwnership _out446;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
            (this).GenExpr(_2132_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out445, out _out446, out _out447);
            _2137_indexR = _out445;
            _2138_indexOwnership = _out446;
            _2139_indexIdents = _out447;
            RAST._IExpr _2140_valueR;
            DCOMP._IOwnership _2141_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2142_valueIdents;
            RAST._IExpr _out448;
            DCOMP._IOwnership _out449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out450;
            (this).GenExpr(_2133_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out448, out _out449, out _out450);
            _2140_valueR = _out448;
            _2141_valueOwnership = _out449;
            _2142_valueIdents = _out450;
            r = ((_2134_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2137_indexR, _2140_valueR));
            RAST._IExpr _out451;
            DCOMP._IOwnership _out452;
            (this).FromOwned(r, expectedOwnership, out _out451, out _out452);
            r = _out451;
            resultingOwnership = _out452;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2136_exprIdents, _2139_indexIdents), _2142_valueIdents);
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_MapUpdate) {
          DAST._IExpression _2143_expr = _source111.dtor_expr;
          DAST._IExpression _2144_index = _source111.dtor_indexExpr;
          DAST._IExpression _2145_value = _source111.dtor_value;
          unmatched111 = false;
          {
            RAST._IExpr _2146_exprR;
            DCOMP._IOwnership _2147___v184;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2148_exprIdents;
            RAST._IExpr _out453;
            DCOMP._IOwnership _out454;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out455;
            (this).GenExpr(_2143_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out453, out _out454, out _out455);
            _2146_exprR = _out453;
            _2147___v184 = _out454;
            _2148_exprIdents = _out455;
            RAST._IExpr _2149_indexR;
            DCOMP._IOwnership _2150_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2151_indexIdents;
            RAST._IExpr _out456;
            DCOMP._IOwnership _out457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out458;
            (this).GenExpr(_2144_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out456, out _out457, out _out458);
            _2149_indexR = _out456;
            _2150_indexOwnership = _out457;
            _2151_indexIdents = _out458;
            RAST._IExpr _2152_valueR;
            DCOMP._IOwnership _2153_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2154_valueIdents;
            RAST._IExpr _out459;
            DCOMP._IOwnership _out460;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out461;
            (this).GenExpr(_2145_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out459, out _out460, out _out461);
            _2152_valueR = _out459;
            _2153_valueOwnership = _out460;
            _2154_valueIdents = _out461;
            r = ((_2146_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2149_indexR, _2152_valueR));
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            (this).FromOwned(r, expectedOwnership, out _out462, out _out463);
            r = _out462;
            resultingOwnership = _out463;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2148_exprIdents, _2151_indexIdents), _2154_valueIdents);
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
                Dafny.ISequence<Dafny.Rune> _2155_id = _source112.dtor_rSelfName;
                DAST._IType _2156_dafnyType = _source112.dtor_dafnyType;
                unmatched112 = false;
                {
                  RAST._IExpr _out464;
                  DCOMP._IOwnership _out465;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
                  (this).GenIdent(_2155_id, selfIdent, env, expectedOwnership, out _out464, out _out465, out _out466);
                  r = _out464;
                  resultingOwnership = _out465;
                  readIdents = _out466;
                }
              }
            }
            if (unmatched112) {
              DCOMP._ISelfInfo _2157_None = _source112;
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
          DAST._IExpression _2158_cond = _source111.dtor_cond;
          DAST._IExpression _2159_t = _source111.dtor_thn;
          DAST._IExpression _2160_f = _source111.dtor_els;
          unmatched111 = false;
          {
            RAST._IExpr _2161_cond;
            DCOMP._IOwnership _2162___v185;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2163_recIdentsCond;
            RAST._IExpr _out469;
            DCOMP._IOwnership _out470;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out471;
            (this).GenExpr(_2158_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out469, out _out470, out _out471);
            _2161_cond = _out469;
            _2162___v185 = _out470;
            _2163_recIdentsCond = _out471;
            RAST._IExpr _2164_fExpr;
            DCOMP._IOwnership _2165_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2166_recIdentsF;
            RAST._IExpr _out472;
            DCOMP._IOwnership _out473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
            (this).GenExpr(_2160_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out472, out _out473, out _out474);
            _2164_fExpr = _out472;
            _2165_fOwned = _out473;
            _2166_recIdentsF = _out474;
            RAST._IExpr _2167_tExpr;
            DCOMP._IOwnership _2168___v186;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2169_recIdentsT;
            RAST._IExpr _out475;
            DCOMP._IOwnership _out476;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out477;
            (this).GenExpr(_2159_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out475, out _out476, out _out477);
            _2167_tExpr = _out475;
            _2168___v186 = _out476;
            _2169_recIdentsT = _out477;
            r = RAST.Expr.create_IfExpr(_2161_cond, _2167_tExpr, _2164_fExpr);
            RAST._IExpr _out478;
            DCOMP._IOwnership _out479;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out478, out _out479);
            r = _out478;
            resultingOwnership = _out479;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2163_recIdentsCond, _2169_recIdentsT), _2166_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source111.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _2170_e = _source111.dtor_expr;
            DAST.Format._IUnaryOpFormat _2171_format = _source111.dtor_format1;
            unmatched111 = false;
            {
              RAST._IExpr _2172_recursiveGen;
              DCOMP._IOwnership _2173___v187;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2174_recIdents;
              RAST._IExpr _out480;
              DCOMP._IOwnership _out481;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out482;
              (this).GenExpr(_2170_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out480, out _out481, out _out482);
              _2172_recursiveGen = _out480;
              _2173___v187 = _out481;
              _2174_recIdents = _out482;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _2172_recursiveGen, _2171_format);
              RAST._IExpr _out483;
              DCOMP._IOwnership _out484;
              (this).FromOwned(r, expectedOwnership, out _out483, out _out484);
              r = _out483;
              resultingOwnership = _out484;
              readIdents = _2174_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source111.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _2175_e = _source111.dtor_expr;
            DAST.Format._IUnaryOpFormat _2176_format = _source111.dtor_format1;
            unmatched111 = false;
            {
              RAST._IExpr _2177_recursiveGen;
              DCOMP._IOwnership _2178___v188;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2179_recIdents;
              RAST._IExpr _out485;
              DCOMP._IOwnership _out486;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out487;
              (this).GenExpr(_2175_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out485, out _out486, out _out487);
              _2177_recursiveGen = _out485;
              _2178___v188 = _out486;
              _2179_recIdents = _out487;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _2177_recursiveGen, _2176_format);
              RAST._IExpr _out488;
              DCOMP._IOwnership _out489;
              (this).FromOwned(r, expectedOwnership, out _out488, out _out489);
              r = _out488;
              resultingOwnership = _out489;
              readIdents = _2179_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source111.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _2180_e = _source111.dtor_expr;
            DAST.Format._IUnaryOpFormat _2181_format = _source111.dtor_format1;
            unmatched111 = false;
            {
              RAST._IExpr _2182_recursiveGen;
              DCOMP._IOwnership _2183_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2184_recIdents;
              RAST._IExpr _out490;
              DCOMP._IOwnership _out491;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out492;
              (this).GenExpr(_2180_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out490, out _out491, out _out492);
              _2182_recursiveGen = _out490;
              _2183_recOwned = _out491;
              _2184_recIdents = _out492;
              r = ((_2182_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out493;
              DCOMP._IOwnership _out494;
              (this).FromOwned(r, expectedOwnership, out _out493, out _out494);
              r = _out493;
              resultingOwnership = _out494;
              readIdents = _2184_recIdents;
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
          DAST._IExpression _2185_expr = _source111.dtor_expr;
          DAST._IType _2186_exprType = _source111.dtor_exprType;
          BigInteger _2187_dim = _source111.dtor_dim;
          bool _2188_native = _source111.dtor_native;
          unmatched111 = false;
          {
            RAST._IExpr _2189_recursiveGen;
            DCOMP._IOwnership _2190___v193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2191_recIdents;
            RAST._IExpr _out498;
            DCOMP._IOwnership _out499;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
            (this).GenExpr(_2185_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out498, out _out499, out _out500);
            _2189_recursiveGen = _out498;
            _2190___v193 = _out499;
            _2191_recIdents = _out500;
            RAST._IType _2192_arrayType;
            RAST._IType _out501;
            _out501 = (this).GenType(_2186_exprType, DCOMP.GenTypeContext.@default());
            _2192_arrayType = _out501;
            if (!((_2192_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2193_msg;
              _2193_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2192_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2193_msg);
              r = RAST.Expr.create_RawExpr(_2193_msg);
            } else {
              RAST._IType _2194_underlying;
              _2194_underlying = (_2192_arrayType).ObjectOrPointerUnderlying();
              if (((_2187_dim).Sign == 0) && ((_2194_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2189_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2187_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2189_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_2189_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_2187_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_2188_native)) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(r);
              }
            }
            RAST._IExpr _out502;
            DCOMP._IOwnership _out503;
            (this).FromOwned(r, expectedOwnership, out _out502, out _out503);
            r = _out502;
            resultingOwnership = _out503;
            readIdents = _2191_recIdents;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_MapKeys) {
          DAST._IExpression _2195_expr = _source111.dtor_expr;
          unmatched111 = false;
          {
            RAST._IExpr _2196_recursiveGen;
            DCOMP._IOwnership _2197___v194;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2198_recIdents;
            RAST._IExpr _out504;
            DCOMP._IOwnership _out505;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out506;
            (this).GenExpr(_2195_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out504, out _out505, out _out506);
            _2196_recursiveGen = _out504;
            _2197___v194 = _out505;
            _2198_recIdents = _out506;
            readIdents = _2198_recIdents;
            r = ((_2196_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _2199_expr = _source111.dtor_expr;
          unmatched111 = false;
          {
            RAST._IExpr _2200_recursiveGen;
            DCOMP._IOwnership _2201___v195;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2202_recIdents;
            RAST._IExpr _out509;
            DCOMP._IOwnership _out510;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out511;
            (this).GenExpr(_2199_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out509, out _out510, out _out511);
            _2200_recursiveGen = _out509;
            _2201___v195 = _out510;
            _2202_recIdents = _out511;
            readIdents = _2202_recIdents;
            r = ((_2200_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _2203_expr = _source111.dtor_expr;
          unmatched111 = false;
          {
            RAST._IExpr _2204_recursiveGen;
            DCOMP._IOwnership _2205___v196;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2206_recIdents;
            RAST._IExpr _out514;
            DCOMP._IOwnership _out515;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out516;
            (this).GenExpr(_2203_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out514, out _out515, out _out516);
            _2204_recursiveGen = _out514;
            _2205___v196 = _out515;
            _2206_recIdents = _out516;
            readIdents = _2206_recIdents;
            r = ((_2204_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("items"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _2207_on = _source111.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2208_field = _source111.dtor_field;
          bool _2209_isDatatype = _source111.dtor_onDatatype;
          bool _2210_isStatic = _source111.dtor_isStatic;
          bool _2211_isConstant = _source111.dtor_isConstant;
          Dafny.ISequence<DAST._IType> _2212_arguments = _source111.dtor_arguments;
          unmatched111 = false;
          {
            RAST._IExpr _2213_onExpr;
            DCOMP._IOwnership _2214_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2215_recIdents;
            RAST._IExpr _out519;
            DCOMP._IOwnership _out520;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
            (this).GenExpr(_2207_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out519, out _out520, out _out521);
            _2213_onExpr = _out519;
            _2214_onOwned = _out520;
            _2215_recIdents = _out521;
            Dafny.ISequence<Dafny.Rune> _2216_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2217_onString;
            _2217_onString = (_2213_onExpr)._ToString(DCOMP.__default.IND);
            if (_2210_isStatic) {
              DCOMP._IEnvironment _2218_lEnv;
              _2218_lEnv = env;
              Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>> _2219_args;
              _2219_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements();
              _2216_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|");
              BigInteger _hi47 = new BigInteger((_2212_arguments).Count);
              for (BigInteger _2220_i = BigInteger.Zero; _2220_i < _hi47; _2220_i++) {
                if ((_2220_i).Sign == 1) {
                  _2216_s = Dafny.Sequence<Dafny.Rune>.Concat(_2216_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                RAST._IType _2221_ty;
                RAST._IType _out522;
                _out522 = (this).GenType((_2212_arguments).Select(_2220_i), DCOMP.GenTypeContext.@default());
                _2221_ty = _out522;
                RAST._IType _2222_bTy;
                _2222_bTy = RAST.Type.create_Borrowed(_2221_ty);
                Dafny.ISequence<Dafny.Rune> _2223_name;
                _2223_name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), Std.Strings.__default.OfInt(_2220_i));
                _2218_lEnv = (_2218_lEnv).AddAssigned(_2223_name, _2222_bTy);
                _2219_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.Concat(_2219_args, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>.create(_2223_name, _2221_ty)));
                _2216_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2216_s, _2223_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_2222_bTy)._ToString(DCOMP.__default.IND));
              }
              _2216_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2216_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| ")), _2217_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeVar(_2208_field)), ((_2211_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("));
              BigInteger _hi48 = new BigInteger((_2219_args).Count);
              for (BigInteger _2224_i = BigInteger.Zero; _2224_i < _hi48; _2224_i++) {
                if ((_2224_i).Sign == 1) {
                  _2216_s = Dafny.Sequence<Dafny.Rune>.Concat(_2216_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType> _let_tmp_rhs70 = (_2219_args).Select(_2224_i);
                Dafny.ISequence<Dafny.Rune> _2225_name = _let_tmp_rhs70.dtor__0;
                RAST._IType _2226_ty = _let_tmp_rhs70.dtor__1;
                RAST._IExpr _2227_rIdent;
                DCOMP._IOwnership _2228___v197;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2229___v198;
                RAST._IExpr _out523;
                DCOMP._IOwnership _out524;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
                (this).GenIdent(_2225_name, selfIdent, _2218_lEnv, (((_2226_ty).CanReadWithoutClone()) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed())), out _out523, out _out524, out _out525);
                _2227_rIdent = _out523;
                _2228___v197 = _out524;
                _2229___v198 = _out525;
                _2216_s = Dafny.Sequence<Dafny.Rune>.Concat(_2216_s, (_2227_rIdent)._ToString(DCOMP.__default.IND));
              }
              _2216_s = Dafny.Sequence<Dafny.Rune>.Concat(_2216_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            } else {
              _2216_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2216_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2216_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2217_onString), ((object.Equals(_2214_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2230_args;
              _2230_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2231_i;
              _2231_i = BigInteger.Zero;
              while ((_2231_i) < (new BigInteger((_2212_arguments).Count))) {
                if ((_2231_i).Sign == 1) {
                  _2230_args = Dafny.Sequence<Dafny.Rune>.Concat(_2230_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2230_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2230_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2231_i));
                _2231_i = (_2231_i) + (BigInteger.One);
              }
              _2216_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2216_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2230_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2216_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2216_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeVar(_2208_field)), ((_2211_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2230_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2216_s = Dafny.Sequence<Dafny.Rune>.Concat(_2216_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2216_s = Dafny.Sequence<Dafny.Rune>.Concat(_2216_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2232_typeShape;
            _2232_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2233_i;
            _2233_i = BigInteger.Zero;
            while ((_2233_i) < (new BigInteger((_2212_arguments).Count))) {
              if ((_2233_i).Sign == 1) {
                _2232_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2232_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2232_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2232_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2233_i = (_2233_i) + (BigInteger.One);
            }
            _2232_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2232_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2216_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2216_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2232_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2216_s);
            RAST._IExpr _out526;
            DCOMP._IOwnership _out527;
            (this).FromOwned(r, expectedOwnership, out _out526, out _out527);
            r = _out526;
            resultingOwnership = _out527;
            readIdents = _2215_recIdents;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_Select) {
          DAST._IExpression _2234_on = _source111.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2235_field = _source111.dtor_field;
          bool _2236_isConstant = _source111.dtor_isConstant;
          bool _2237_isDatatype = _source111.dtor_onDatatype;
          DAST._IType _2238_fieldType = _source111.dtor_fieldType;
          unmatched111 = false;
          {
            if (((_2234_on).is_Companion) || ((_2234_on).is_ExternCompanion)) {
              RAST._IExpr _2239_onExpr;
              DCOMP._IOwnership _2240_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2241_recIdents;
              RAST._IExpr _out528;
              DCOMP._IOwnership _out529;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
              (this).GenExpr(_2234_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out528, out _out529, out _out530);
              _2239_onExpr = _out528;
              _2240_onOwned = _out529;
              _2241_recIdents = _out530;
              r = ((_2239_onExpr).FSel(DCOMP.__default.escapeVar(_2235_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out531;
              DCOMP._IOwnership _out532;
              (this).FromOwned(r, expectedOwnership, out _out531, out _out532);
              r = _out531;
              resultingOwnership = _out532;
              readIdents = _2241_recIdents;
              return ;
            } else if (_2237_isDatatype) {
              RAST._IExpr _2242_onExpr;
              DCOMP._IOwnership _2243_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2244_recIdents;
              RAST._IExpr _out533;
              DCOMP._IOwnership _out534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
              (this).GenExpr(_2234_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out533, out _out534, out _out535);
              _2242_onExpr = _out533;
              _2243_onOwned = _out534;
              _2244_recIdents = _out535;
              r = ((_2242_onExpr).Sel(DCOMP.__default.escapeVar(_2235_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2245_typ;
              RAST._IType _out536;
              _out536 = (this).GenType(_2238_fieldType, DCOMP.GenTypeContext.@default());
              _2245_typ = _out536;
              RAST._IExpr _out537;
              DCOMP._IOwnership _out538;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out537, out _out538);
              r = _out537;
              resultingOwnership = _out538;
              readIdents = _2244_recIdents;
            } else {
              RAST._IExpr _2246_onExpr;
              DCOMP._IOwnership _2247_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2248_recIdents;
              RAST._IExpr _out539;
              DCOMP._IOwnership _out540;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
              (this).GenExpr(_2234_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out539, out _out540, out _out541);
              _2246_onExpr = _out539;
              _2247_onOwned = _out540;
              _2248_recIdents = _out541;
              r = _2246_onExpr;
              if (!object.Equals(_2246_onExpr, RAST.__default.self)) {
                RAST._IExpr _source113 = _2246_onExpr;
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
              r = (r).Sel(DCOMP.__default.escapeVar(_2235_field));
              if (_2236_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out542;
              DCOMP._IOwnership _out543;
              (this).FromOwned(r, expectedOwnership, out _out542, out _out543);
              r = _out542;
              resultingOwnership = _out543;
              readIdents = _2248_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_Index) {
          DAST._IExpression _2249_on = _source111.dtor_expr;
          DAST._ICollKind _2250_collKind = _source111.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2251_indices = _source111.dtor_indices;
          unmatched111 = false;
          {
            RAST._IExpr _2252_onExpr;
            DCOMP._IOwnership _2253_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2254_recIdents;
            RAST._IExpr _out544;
            DCOMP._IOwnership _out545;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out546;
            (this).GenExpr(_2249_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out544, out _out545, out _out546);
            _2252_onExpr = _out544;
            _2253_onOwned = _out545;
            _2254_recIdents = _out546;
            readIdents = _2254_recIdents;
            r = _2252_onExpr;
            bool _2255_hadArray;
            _2255_hadArray = false;
            if (object.Equals(_2250_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2255_hadArray = true;
              if ((new BigInteger((_2251_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi49 = new BigInteger((_2251_indices).Count);
            for (BigInteger _2256_i = BigInteger.Zero; _2256_i < _hi49; _2256_i++) {
              if (object.Equals(_2250_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2257_idx;
                DCOMP._IOwnership _2258_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2259_recIdentsIdx;
                RAST._IExpr _out547;
                DCOMP._IOwnership _out548;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
                (this).GenExpr((_2251_indices).Select(_2256_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out547, out _out548, out _out549);
                _2257_idx = _out547;
                _2258_idxOwned = _out548;
                _2259_recIdentsIdx = _out549;
                _2257_idx = RAST.__default.IntoUsize(_2257_idx);
                r = RAST.Expr.create_SelectIndex(r, _2257_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2259_recIdentsIdx);
              } else {
                RAST._IExpr _2260_idx;
                DCOMP._IOwnership _2261_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2262_recIdentsIdx;
                RAST._IExpr _out550;
                DCOMP._IOwnership _out551;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
                (this).GenExpr((_2251_indices).Select(_2256_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out550, out _out551, out _out552);
                _2260_idx = _out550;
                _2261_idxOwned = _out551;
                _2262_recIdentsIdx = _out552;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2260_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2262_recIdentsIdx);
              }
            }
            if (_2255_hadArray) {
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
          DAST._IExpression _2263_on = _source111.dtor_expr;
          bool _2264_isArray = _source111.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2265_low = _source111.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2266_high = _source111.dtor_high;
          unmatched111 = false;
          {
            RAST._IExpr _2267_onExpr;
            DCOMP._IOwnership _2268_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2269_recIdents;
            RAST._IExpr _out555;
            DCOMP._IOwnership _out556;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
            (this).GenExpr(_2263_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out555, out _out556, out _out557);
            _2267_onExpr = _out555;
            _2268_onOwned = _out556;
            _2269_recIdents = _out557;
            readIdents = _2269_recIdents;
            Dafny.ISequence<Dafny.Rune> _2270_methodName;
            _2270_methodName = (((_2265_low).is_Some) ? ((((_2266_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2266_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2271_arguments;
            _2271_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source114 = _2265_low;
            bool unmatched114 = true;
            if (unmatched114) {
              if (_source114.is_Some) {
                DAST._IExpression _2272_l = _source114.dtor_value;
                unmatched114 = false;
                {
                  RAST._IExpr _2273_lExpr;
                  DCOMP._IOwnership _2274___v201;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2275_recIdentsL;
                  RAST._IExpr _out558;
                  DCOMP._IOwnership _out559;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
                  (this).GenExpr(_2272_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out558, out _out559, out _out560);
                  _2273_lExpr = _out558;
                  _2274___v201 = _out559;
                  _2275_recIdentsL = _out560;
                  _2271_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2271_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2273_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2275_recIdentsL);
                }
              }
            }
            if (unmatched114) {
              unmatched114 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source115 = _2266_high;
            bool unmatched115 = true;
            if (unmatched115) {
              if (_source115.is_Some) {
                DAST._IExpression _2276_h = _source115.dtor_value;
                unmatched115 = false;
                {
                  RAST._IExpr _2277_hExpr;
                  DCOMP._IOwnership _2278___v202;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2279_recIdentsH;
                  RAST._IExpr _out561;
                  DCOMP._IOwnership _out562;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
                  (this).GenExpr(_2276_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out561, out _out562, out _out563);
                  _2277_hExpr = _out561;
                  _2278___v202 = _out562;
                  _2279_recIdentsH = _out563;
                  _2271_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2271_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2277_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2279_recIdentsH);
                }
              }
            }
            if (unmatched115) {
              unmatched115 = false;
            }
            r = _2267_onExpr;
            if (_2264_isArray) {
              if (!(_2270_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2270_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2270_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).FSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2270_methodName))).Apply(_2271_arguments);
            } else {
              if (!(_2270_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2270_methodName)).Apply(_2271_arguments);
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
          DAST._IExpression _2280_on = _source111.dtor_expr;
          BigInteger _2281_idx = _source111.dtor_index;
          DAST._IType _2282_fieldType = _source111.dtor_fieldType;
          unmatched111 = false;
          {
            RAST._IExpr _2283_onExpr;
            DCOMP._IOwnership _2284_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2285_recIdents;
            RAST._IExpr _out566;
            DCOMP._IOwnership _out567;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
            (this).GenExpr(_2280_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out566, out _out567, out _out568);
            _2283_onExpr = _out566;
            _2284_onOwnership = _out567;
            _2285_recIdents = _out568;
            Dafny.ISequence<Dafny.Rune> _2286_selName;
            _2286_selName = Std.Strings.__default.OfNat(_2281_idx);
            DAST._IType _source116 = _2282_fieldType;
            bool unmatched116 = true;
            if (unmatched116) {
              if (_source116.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2287_tps = _source116.dtor_Tuple_a0;
                unmatched116 = false;
                if (((_2282_fieldType).is_Tuple) && ((new BigInteger((_2287_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2286_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2286_selName);
                }
              }
            }
            if (unmatched116) {
              unmatched116 = false;
            }
            r = ((_2283_onExpr).Sel(_2286_selName)).Clone();
            RAST._IExpr _out569;
            DCOMP._IOwnership _out570;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out569, out _out570);
            r = _out569;
            resultingOwnership = _out570;
            readIdents = _2285_recIdents;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_Call) {
          DAST._IExpression _2288_on = _source111.dtor_on;
          DAST._ICallName _2289_name = _source111.dtor_callName;
          Dafny.ISequence<DAST._IType> _2290_typeArgs = _source111.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2291_args = _source111.dtor_args;
          unmatched111 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2292_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2293_recIdents;
            Dafny.ISequence<RAST._IType> _2294_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2295_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out571;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out572;
            Dafny.ISequence<RAST._IType> _out573;
            Std.Wrappers._IOption<DAST._IResolvedType> _out574;
            (this).GenArgs(selfIdent, _2289_name, _2290_typeArgs, _2291_args, env, out _out571, out _out572, out _out573, out _out574);
            _2292_argExprs = _out571;
            _2293_recIdents = _out572;
            _2294_typeExprs = _out573;
            _2295_fullNameQualifier = _out574;
            readIdents = _2293_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source117 = _2295_fullNameQualifier;
            bool unmatched117 = true;
            if (unmatched117) {
              if (_source117.is_Some) {
                DAST._IResolvedType value11 = _source117.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2296_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2297_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2298_base = value11.dtor_kind;
                unmatched117 = false;
                RAST._IExpr _2299_fullPath;
                RAST._IExpr _out575;
                _out575 = DCOMP.COMP.GenPathExpr(_2296_path, true);
                _2299_fullPath = _out575;
                Dafny.ISequence<RAST._IType> _2300_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out576;
                _out576 = (this).GenTypeArgs(_2297_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2300_onTypeExprs = _out576;
                RAST._IExpr _2301_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2302_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2303_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2298_base).is_Trait) || ((_2298_base).is_Class)) {
                  RAST._IExpr _out577;
                  DCOMP._IOwnership _out578;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out579;
                  (this).GenExpr(_2288_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out577, out _out578, out _out579);
                  _2301_onExpr = _out577;
                  _2302_recOwnership = _out578;
                  _2303_recIdents = _out579;
                  _2301_onExpr = ((this).read__macro).Apply1(_2301_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2303_recIdents);
                } else {
                  RAST._IExpr _out580;
                  DCOMP._IOwnership _out581;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out582;
                  (this).GenExpr(_2288_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out580, out _out581, out _out582);
                  _2301_onExpr = _out580;
                  _2302_recOwnership = _out581;
                  _2303_recIdents = _out582;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2303_recIdents);
                }
                r = ((((_2299_fullPath).ApplyType(_2300_onTypeExprs)).FSel(DCOMP.__default.escapeName((_2289_name).dtor_name))).ApplyType(_2294_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2301_onExpr), _2292_argExprs));
                RAST._IExpr _out583;
                DCOMP._IOwnership _out584;
                (this).FromOwned(r, expectedOwnership, out _out583, out _out584);
                r = _out583;
                resultingOwnership = _out584;
              }
            }
            if (unmatched117) {
              unmatched117 = false;
              RAST._IExpr _2304_onExpr;
              DCOMP._IOwnership _2305___v208;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2306_recIdents;
              RAST._IExpr _out585;
              DCOMP._IOwnership _out586;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out587;
              (this).GenExpr(_2288_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out585, out _out586, out _out587);
              _2304_onExpr = _out585;
              _2305___v208 = _out586;
              _2306_recIdents = _out587;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2306_recIdents);
              Dafny.ISequence<Dafny.Rune> _2307_renderedName;
              _2307_renderedName = (this).GetMethodName(_2288_on, _2289_name);
              DAST._IExpression _source118 = _2288_on;
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
                    _2304_onExpr = (_2304_onExpr).FSel(_2307_renderedName);
                  }
                }
              }
              if (unmatched118) {
                unmatched118 = false;
                {
                  if (!object.Equals(_2304_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source119 = _2289_name;
                    bool unmatched119 = true;
                    if (unmatched119) {
                      if (_source119.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source119.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2308_tpe = onType2.dtor_value;
                          unmatched119 = false;
                          RAST._IType _2309_typ;
                          RAST._IType _out588;
                          _out588 = (this).GenType(_2308_tpe, DCOMP.GenTypeContext.@default());
                          _2309_typ = _out588;
                          if ((_2309_typ).IsObjectOrPointer()) {
                            _2304_onExpr = ((this).read__macro).Apply1(_2304_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched119) {
                      unmatched119 = false;
                    }
                  }
                  _2304_onExpr = (_2304_onExpr).Sel(_2307_renderedName);
                }
              }
              r = ((_2304_onExpr).ApplyType(_2294_typeExprs)).Apply(_2292_argExprs);
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
          Dafny.ISequence<DAST._IFormal> _2310_paramsDafny = _source111.dtor_params;
          DAST._IType _2311_retType = _source111.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2312_body = _source111.dtor_body;
          unmatched111 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2313_params;
            Dafny.ISequence<RAST._IFormal> _out591;
            _out591 = (this).GenParams(_2310_paramsDafny, true);
            _2313_params = _out591;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2314_paramNames;
            _2314_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2315_paramTypesMap;
            _2315_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi50 = new BigInteger((_2313_params).Count);
            for (BigInteger _2316_i = BigInteger.Zero; _2316_i < _hi50; _2316_i++) {
              Dafny.ISequence<Dafny.Rune> _2317_name;
              _2317_name = ((_2313_params).Select(_2316_i)).dtor_name;
              _2314_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2314_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2317_name));
              _2315_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2315_paramTypesMap, _2317_name, ((_2313_params).Select(_2316_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2318_subEnv;
            _2318_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2314_paramNames, _2315_paramTypesMap));
            RAST._IExpr _2319_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2320_recIdents;
            DCOMP._IEnvironment _2321___v218;
            RAST._IExpr _out592;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out593;
            DCOMP._IEnvironment _out594;
            (this).GenStmts(_2312_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2318_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out592, out _out593, out _out594);
            _2319_recursiveGen = _out592;
            _2320_recIdents = _out593;
            _2321___v218 = _out594;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2320_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2320_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2322_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll10 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_11 in (_2322_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2323_name = (Dafny.ISequence<Dafny.Rune>)_compr_11;
                if ((_2322_paramNames).Contains(_2323_name)) {
                  _coll10.Add(_2323_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll10);
            }))())(_2314_paramNames));
            RAST._IExpr _2324_allReadCloned;
            _2324_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2320_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2325_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_4 in (_2320_recIdents).Elements) {
                _2325_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_4;
                if ((_2320_recIdents).Contains(_2325_next)) {
                  goto after__ASSIGN_SUCH_THAT_4;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 5242)");
            after__ASSIGN_SUCH_THAT_4: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2325_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2326_selfCloned;
                DCOMP._IOwnership _2327___v219;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2328___v220;
                RAST._IExpr _out595;
                DCOMP._IOwnership _out596;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out597;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out595, out _out596, out _out597);
                _2326_selfCloned = _out595;
                _2327___v219 = _out596;
                _2328___v220 = _out597;
                _2324_allReadCloned = (_2324_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2326_selfCloned)));
              } else if (!((_2314_paramNames).Contains(_2325_next))) {
                RAST._IExpr _2329_copy;
                _2329_copy = (RAST.Expr.create_Identifier(_2325_next)).Clone();
                _2324_allReadCloned = (_2324_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2325_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2329_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2325_next));
              }
              _2320_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2320_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2325_next));
            }
            RAST._IType _2330_retTypeGen;
            RAST._IType _out598;
            _out598 = (this).GenType(_2311_retType, DCOMP.GenTypeContext.@default());
            _2330_retTypeGen = _out598;
            r = RAST.Expr.create_Block((_2324_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2313_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2330_retTypeGen), RAST.Expr.create_Block(_2319_recursiveGen)))));
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
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2331_values = _source111.dtor_values;
          DAST._IType _2332_retType = _source111.dtor_retType;
          DAST._IExpression _2333_expr = _source111.dtor_expr;
          unmatched111 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2334_paramNames;
            _2334_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2335_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out601;
            _out601 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2336_value) => {
              return (_2336_value).dtor__0;
            })), _2331_values), false);
            _2335_paramFormals = _out601;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2337_paramTypes;
            _2337_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2338_paramNamesSet;
            _2338_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi51 = new BigInteger((_2331_values).Count);
            for (BigInteger _2339_i = BigInteger.Zero; _2339_i < _hi51; _2339_i++) {
              Dafny.ISequence<Dafny.Rune> _2340_name;
              _2340_name = (((_2331_values).Select(_2339_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2341_rName;
              _2341_rName = DCOMP.__default.escapeVar(_2340_name);
              _2334_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2334_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2341_rName));
              _2337_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2337_paramTypes, _2341_rName, ((_2335_paramFormals).Select(_2339_i)).dtor_tpe);
              _2338_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2338_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2341_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi52 = new BigInteger((_2331_values).Count);
            for (BigInteger _2342_i = BigInteger.Zero; _2342_i < _hi52; _2342_i++) {
              RAST._IType _2343_typeGen;
              RAST._IType _out602;
              _out602 = (this).GenType((((_2331_values).Select(_2342_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.@default());
              _2343_typeGen = _out602;
              RAST._IExpr _2344_valueGen;
              DCOMP._IOwnership _2345___v221;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2346_recIdents;
              RAST._IExpr _out603;
              DCOMP._IOwnership _out604;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out605;
              (this).GenExpr(((_2331_values).Select(_2342_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out603, out _out604, out _out605);
              _2344_valueGen = _out603;
              _2345___v221 = _out604;
              _2346_recIdents = _out605;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar((((_2331_values).Select(_2342_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2343_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2344_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2346_recIdents);
            }
            DCOMP._IEnvironment _2347_newEnv;
            _2347_newEnv = DCOMP.Environment.create(_2334_paramNames, _2337_paramTypes);
            RAST._IExpr _2348_recGen;
            DCOMP._IOwnership _2349_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2350_recIdents;
            RAST._IExpr _out606;
            DCOMP._IOwnership _out607;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out608;
            (this).GenExpr(_2333_expr, selfIdent, _2347_newEnv, expectedOwnership, out _out606, out _out607, out _out608);
            _2348_recGen = _out606;
            _2349_recOwned = _out607;
            _2350_recIdents = _out608;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2350_recIdents, _2338_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2348_recGen));
            RAST._IExpr _out609;
            DCOMP._IOwnership _out610;
            (this).FromOwnership(r, _2349_recOwned, expectedOwnership, out _out609, out _out610);
            r = _out609;
            resultingOwnership = _out610;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2351_name = _source111.dtor_ident;
          DAST._IType _2352_tpe = _source111.dtor_typ;
          DAST._IExpression _2353_value = _source111.dtor_value;
          DAST._IExpression _2354_iifeBody = _source111.dtor_iifeBody;
          unmatched111 = false;
          {
            RAST._IExpr _2355_valueGen;
            DCOMP._IOwnership _2356___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2357_recIdents;
            RAST._IExpr _out611;
            DCOMP._IOwnership _out612;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out613;
            (this).GenExpr(_2353_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out611, out _out612, out _out613);
            _2355_valueGen = _out611;
            _2356___v222 = _out612;
            _2357_recIdents = _out613;
            readIdents = _2357_recIdents;
            RAST._IType _2358_valueTypeGen;
            RAST._IType _out614;
            _out614 = (this).GenType(_2352_tpe, DCOMP.GenTypeContext.@default());
            _2358_valueTypeGen = _out614;
            Dafny.ISequence<Dafny.Rune> _2359_iifeVar;
            _2359_iifeVar = DCOMP.__default.escapeVar(_2351_name);
            RAST._IExpr _2360_bodyGen;
            DCOMP._IOwnership _2361___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2362_bodyIdents;
            RAST._IExpr _out615;
            DCOMP._IOwnership _out616;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out617;
            (this).GenExpr(_2354_iifeBody, selfIdent, (env).AddAssigned(_2359_iifeVar, _2358_valueTypeGen), DCOMP.Ownership.create_OwnershipOwned(), out _out615, out _out616, out _out617);
            _2360_bodyGen = _out615;
            _2361___v223 = _out616;
            _2362_bodyIdents = _out617;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2362_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2359_iifeVar)));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _2359_iifeVar, Std.Wrappers.Option<RAST._IType>.create_Some(_2358_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2355_valueGen))).Then(_2360_bodyGen));
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
          DAST._IExpression _2363_func = _source111.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2364_args = _source111.dtor_args;
          unmatched111 = false;
          {
            RAST._IExpr _2365_funcExpr;
            DCOMP._IOwnership _2366___v224;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2367_recIdents;
            RAST._IExpr _out620;
            DCOMP._IOwnership _out621;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
            (this).GenExpr(_2363_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out620, out _out621, out _out622);
            _2365_funcExpr = _out620;
            _2366___v224 = _out621;
            _2367_recIdents = _out622;
            readIdents = _2367_recIdents;
            Dafny.ISequence<RAST._IExpr> _2368_rArgs;
            _2368_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi53 = new BigInteger((_2364_args).Count);
            for (BigInteger _2369_i = BigInteger.Zero; _2369_i < _hi53; _2369_i++) {
              RAST._IExpr _2370_argExpr;
              DCOMP._IOwnership _2371_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2372_argIdents;
              RAST._IExpr _out623;
              DCOMP._IOwnership _out624;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out625;
              (this).GenExpr((_2364_args).Select(_2369_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out623, out _out624, out _out625);
              _2370_argExpr = _out623;
              _2371_argOwned = _out624;
              _2372_argIdents = _out625;
              _2368_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2368_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2370_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2372_argIdents);
            }
            r = (_2365_funcExpr).Apply(_2368_rArgs);
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
          DAST._IExpression _2373_on = _source111.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2374_dType = _source111.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2375_variant = _source111.dtor_variant;
          unmatched111 = false;
          {
            RAST._IExpr _2376_exprGen;
            DCOMP._IOwnership _2377___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2378_recIdents;
            RAST._IExpr _out628;
            DCOMP._IOwnership _out629;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out630;
            (this).GenExpr(_2373_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out628, out _out629, out _out630);
            _2376_exprGen = _out628;
            _2377___v225 = _out629;
            _2378_recIdents = _out630;
            RAST._IType _2379_dTypePath;
            RAST._IType _out631;
            _out631 = DCOMP.COMP.GenPathType(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2374_dType, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2375_variant)));
            _2379_dTypePath = _out631;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2376_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_2379_dTypePath)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out632;
            DCOMP._IOwnership _out633;
            (this).FromOwned(r, expectedOwnership, out _out632, out _out633);
            r = _out632;
            resultingOwnership = _out633;
            readIdents = _2378_recIdents;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_Is) {
          DAST._IExpression _2380_expr = _source111.dtor_expr;
          DAST._IType _2381_fromType = _source111.dtor_fromType;
          DAST._IType _2382_toType = _source111.dtor_toType;
          unmatched111 = false;
          {
            RAST._IExpr _2383_expr;
            DCOMP._IOwnership _2384_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2385_recIdents;
            RAST._IExpr _out634;
            DCOMP._IOwnership _out635;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out636;
            (this).GenExpr(_2380_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out634, out _out635, out _out636);
            _2383_expr = _out634;
            _2384_recOwned = _out635;
            _2385_recIdents = _out636;
            RAST._IType _2386_fromType;
            RAST._IType _out637;
            _out637 = (this).GenType(_2381_fromType, DCOMP.GenTypeContext.@default());
            _2386_fromType = _out637;
            RAST._IType _2387_toType;
            RAST._IType _out638;
            _out638 = (this).GenType(_2382_toType, DCOMP.GenTypeContext.@default());
            _2387_toType = _out638;
            if (((_2386_fromType).IsObjectOrPointer()) && ((_2387_toType).IsObjectOrPointer())) {
              r = (((_2383_expr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is_instance_of"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((_2387_toType).ObjectOrPointerUnderlying()))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Source and/or target types of type test is/are not Object or Ptr"));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
            RAST._IExpr _out639;
            DCOMP._IOwnership _out640;
            (this).FromOwnership(r, _2384_recOwned, expectedOwnership, out _out639, out _out640);
            r = _out639;
            resultingOwnership = _out640;
            readIdents = _2385_recIdents;
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
          DAST._IExpression _2388_of = _source111.dtor_of;
          unmatched111 = false;
          {
            RAST._IExpr _2389_exprGen;
            DCOMP._IOwnership _2390___v226;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2391_recIdents;
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out645;
            (this).GenExpr(_2388_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out643, out _out644, out _out645);
            _2389_exprGen = _out643;
            _2390___v226 = _out644;
            _2391_recIdents = _out645;
            r = ((_2389_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out646;
            DCOMP._IOwnership _out647;
            (this).FromOwned(r, expectedOwnership, out _out646, out _out647);
            r = _out646;
            resultingOwnership = _out647;
            readIdents = _2391_recIdents;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_SeqBoundedPool) {
          DAST._IExpression _2392_of = _source111.dtor_of;
          bool _2393_includeDuplicates = _source111.dtor_includeDuplicates;
          unmatched111 = false;
          {
            RAST._IExpr _2394_exprGen;
            DCOMP._IOwnership _2395___v227;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2396_recIdents;
            RAST._IExpr _out648;
            DCOMP._IOwnership _out649;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out650;
            (this).GenExpr(_2392_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out648, out _out649, out _out650);
            _2394_exprGen = _out648;
            _2395___v227 = _out649;
            _2396_recIdents = _out650;
            r = ((_2394_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2393_includeDuplicates)) {
              r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).AsExpr()).Apply1(r);
            }
            RAST._IExpr _out651;
            DCOMP._IOwnership _out652;
            (this).FromOwned(r, expectedOwnership, out _out651, out _out652);
            r = _out651;
            resultingOwnership = _out652;
            readIdents = _2396_recIdents;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_MapBoundedPool) {
          DAST._IExpression _2397_of = _source111.dtor_of;
          unmatched111 = false;
          {
            RAST._IExpr _2398_exprGen;
            DCOMP._IOwnership _2399___v228;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2400_recIdents;
            RAST._IExpr _out653;
            DCOMP._IOwnership _out654;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
            (this).GenExpr(_2397_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out653, out _out654, out _out655);
            _2398_exprGen = _out653;
            _2399___v228 = _out654;
            _2400_recIdents = _out655;
            r = ((((_2398_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2400_recIdents;
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
          DAST._IExpression _2401_lo = _source111.dtor_lo;
          DAST._IExpression _2402_hi = _source111.dtor_hi;
          bool _2403_up = _source111.dtor_up;
          unmatched111 = false;
          {
            RAST._IExpr _2404_lo;
            DCOMP._IOwnership _2405___v229;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2406_recIdentsLo;
            RAST._IExpr _out658;
            DCOMP._IOwnership _out659;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out660;
            (this).GenExpr(_2401_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out658, out _out659, out _out660);
            _2404_lo = _out658;
            _2405___v229 = _out659;
            _2406_recIdentsLo = _out660;
            RAST._IExpr _2407_hi;
            DCOMP._IOwnership _2408___v230;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2409_recIdentsHi;
            RAST._IExpr _out661;
            DCOMP._IOwnership _out662;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out663;
            (this).GenExpr(_2402_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out661, out _out662, out _out663);
            _2407_hi = _out661;
            _2408___v230 = _out662;
            _2409_recIdentsHi = _out663;
            if (_2403_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2404_lo, _2407_hi));
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2407_hi, _2404_lo));
            }
            RAST._IExpr _out664;
            DCOMP._IOwnership _out665;
            (this).FromOwned(r, expectedOwnership, out _out664, out _out665);
            r = _out664;
            resultingOwnership = _out665;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2406_recIdentsLo, _2409_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_UnboundedIntRange) {
          DAST._IExpression _2410_start = _source111.dtor_start;
          bool _2411_up = _source111.dtor_up;
          unmatched111 = false;
          {
            RAST._IExpr _2412_start;
            DCOMP._IOwnership _2413___v231;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2414_recIdentStart;
            RAST._IExpr _out666;
            DCOMP._IOwnership _out667;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out668;
            (this).GenExpr(_2410_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out666, out _out667, out _out668);
            _2412_start = _out666;
            _2413___v231 = _out667;
            _2414_recIdentStart = _out668;
            if (_2411_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).AsExpr()).Apply1(_2412_start);
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).AsExpr()).Apply1(_2412_start);
            }
            RAST._IExpr _out669;
            DCOMP._IOwnership _out670;
            (this).FromOwned(r, expectedOwnership, out _out669, out _out670);
            r = _out669;
            resultingOwnership = _out670;
            readIdents = _2414_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched111) {
        if (_source111.is_MapBuilder) {
          DAST._IType _2415_keyType = _source111.dtor_keyType;
          DAST._IType _2416_valueType = _source111.dtor_valueType;
          unmatched111 = false;
          {
            RAST._IType _2417_kType;
            RAST._IType _out671;
            _out671 = (this).GenType(_2415_keyType, DCOMP.GenTypeContext.@default());
            _2417_kType = _out671;
            RAST._IType _2418_vType;
            RAST._IType _out672;
            _out672 = (this).GenType(_2416_valueType, DCOMP.GenTypeContext.@default());
            _2418_vType = _out672;
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2417_kType, _2418_vType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IType _2419_elemType = _source111.dtor_elemType;
          unmatched111 = false;
          {
            RAST._IType _2420_eType;
            RAST._IType _out675;
            _out675 = (this).GenType(_2419_elemType, DCOMP.GenTypeContext.@default());
            _2420_eType = _out675;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2420_eType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
        DAST._IType _2421_elemType = _source111.dtor_elemType;
        DAST._IExpression _2422_collection = _source111.dtor_collection;
        bool _2423_is__forall = _source111.dtor_is__forall;
        DAST._IExpression _2424_lambda = _source111.dtor_lambda;
        unmatched111 = false;
        {
          RAST._IType _2425_tpe;
          RAST._IType _out678;
          _out678 = (this).GenType(_2421_elemType, DCOMP.GenTypeContext.@default());
          _2425_tpe = _out678;
          RAST._IExpr _2426_collectionGen;
          DCOMP._IOwnership _2427___v232;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2428_recIdents;
          RAST._IExpr _out679;
          DCOMP._IOwnership _out680;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out681;
          (this).GenExpr(_2422_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out679, out _out680, out _out681);
          _2426_collectionGen = _out679;
          _2427___v232 = _out680;
          _2428_recIdents = _out681;
          Dafny.ISequence<DAST._IAttribute> _2429_extraAttributes;
          _2429_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2422_collection).is_IntRange) || ((_2422_collection).is_UnboundedIntRange)) || ((_2422_collection).is_SeqBoundedPool)) {
            _2429_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2424_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2430_formals;
            _2430_formals = (_2424_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2431_newFormals;
            _2431_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi54 = new BigInteger((_2430_formals).Count);
            for (BigInteger _2432_i = BigInteger.Zero; _2432_i < _hi54; _2432_i++) {
              var _pat_let_tv200 = _2429_extraAttributes;
              var _pat_let_tv201 = _2430_formals;
              _2431_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2431_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2430_formals).Select(_2432_i), _pat_let29_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let29_0, _2433_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv200, ((_pat_let_tv201).Select(_2432_i)).dtor_attributes), _pat_let30_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let30_0, _2434_dt__update_hattributes_h0 => DAST.Formal.create((_2433_dt__update__tmp_h0).dtor_name, (_2433_dt__update__tmp_h0).dtor_typ, _2434_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv202 = _2431_newFormals;
            DAST._IExpression _2435_newLambda;
            _2435_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2424_lambda, _pat_let31_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let31_0, _2436_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv202, _pat_let32_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let32_0, _2437_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2437_dt__update_hparams_h0, (_2436_dt__update__tmp_h1).dtor_retType, (_2436_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2438_lambdaGen;
            DCOMP._IOwnership _2439___v233;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2440_recLambdaIdents;
            RAST._IExpr _out682;
            DCOMP._IOwnership _out683;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out684;
            (this).GenExpr(_2435_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out682, out _out683, out _out684);
            _2438_lambdaGen = _out682;
            _2439___v233 = _out683;
            _2440_recLambdaIdents = _out684;
            Dafny.ISequence<Dafny.Rune> _2441_fn;
            _2441_fn = ((_2423_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2426_collectionGen).Sel(_2441_fn)).Apply1(((_2438_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2428_recIdents, _2440_recLambdaIdents);
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
      Dafny.ISequence<RAST._IModDecl> _2442_externUseDecls;
      _2442_externUseDecls = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi55 = new BigInteger((externalFiles).Count);
      for (BigInteger _2443_i = BigInteger.Zero; _2443_i < _hi55; _2443_i++) {
        Dafny.ISequence<Dafny.Rune> _2444_externalFile;
        _2444_externalFile = (externalFiles).Select(_2443_i);
        Dafny.ISequence<Dafny.Rune> _2445_externalMod;
        _2445_externalMod = _2444_externalFile;
        if (((new BigInteger((_2444_externalFile).Count)) > (new BigInteger(3))) && (((_2444_externalFile).Drop((new BigInteger((_2444_externalFile).Count)) - (new BigInteger(3)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".rs")))) {
          _2445_externalMod = (_2444_externalFile).Subsequence(BigInteger.Zero, (new BigInteger((_2444_externalFile).Count)) - (new BigInteger(3)));
        } else {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unrecognized external file "), _2444_externalFile), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". External file must be *.rs files")));
        }
        RAST._IMod _2446_externMod;
        _2446_externMod = RAST.Mod.create_ExternMod(_2445_externalMod);
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (_2446_externMod)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        _2442_externUseDecls = Dafny.Sequence<RAST._IModDecl>.Concat(_2442_externUseDecls, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), ((RAST.__default.crate).MSel(_2445_externalMod)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))));
      }
      if (!(_2442_externUseDecls).Equals(Dafny.Sequence<RAST._IModDecl>.FromElements())) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (RAST.Mod.create_Mod(DCOMP.COMP.DAFNY__EXTERN__MODULE, _2442_externUseDecls))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
      }
      DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _2447_allModules;
      _2447_allModules = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Empty();
      BigInteger _hi56 = new BigInteger((p).Count);
      for (BigInteger _2448_i = BigInteger.Zero; _2448_i < _hi56; _2448_i++) {
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _2449_m;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out687;
        _out687 = (this).GenModule((p).Select(_2448_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2449_m = _out687;
        _2447_allModules = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(_2447_allModules, _2449_m);
      }
      BigInteger _hi57 = new BigInteger(((_2447_allModules).dtor_keys).Count);
      for (BigInteger _2450_i = BigInteger.Zero; _2450_i < _hi57; _2450_i++) {
        if (!((_2447_allModules).dtor_values).Contains(((_2447_allModules).dtor_keys).Select(_2450_i))) {
          goto continue_0;
        }
        RAST._IMod _2451_m;
        _2451_m = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Select((_2447_allModules).dtor_values,((_2447_allModules).dtor_keys).Select(_2450_i))).ToRust();
        BigInteger _hi58 = new BigInteger((this.optimizations).Count);
        for (BigInteger _2452_j = BigInteger.Zero; _2452_j < _hi58; _2452_j++) {
          _2451_m = Dafny.Helpers.Id<Func<RAST._IMod, RAST._IMod>>((this.optimizations).Select(_2452_j))(_2451_m);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (_2451_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      continue_0: ;
      }
    after_0: ;
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2453_i;
      _2453_i = BigInteger.Zero;
      while ((_2453_i) < (new BigInteger((fullName).Count))) {
        if ((_2453_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2453_i)));
        _2453_i = (_2453_i) + (BigInteger.One);
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