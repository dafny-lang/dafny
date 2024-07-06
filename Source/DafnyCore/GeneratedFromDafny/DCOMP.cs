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
      Dafny.ISequence<Dafny.Rune> _1282___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1282___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1282___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1282___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(new BigInteger(2));
        i = _in124;
        goto TAIL_CALL_START;
      } else {
        _1282___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1282___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1283___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1283___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1283___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1283___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in126 = (i).Drop(BigInteger.One);
        i = _in126;
        goto TAIL_CALL_START;
      } else {
        _1283___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1283___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1284_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1284_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeVar(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1285_r = (f);
      if ((DCOMP.__default.reserved__vars).Contains(_1285_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1285_r);
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
      var _pat_let_tv194 = dafnyName;
      var _pat_let_tv195 = rs;
      var _pat_let_tv196 = dafnyName;
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _1286_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source63 = (rs).Select(BigInteger.Zero);
          bool unmatched63 = true;
          if (unmatched63) {
            if (_source63.is_UserDefined) {
              DAST._IResolvedType _1287_resolvedType = _source63.dtor_resolved;
              unmatched63 = false;
              return DCOMP.__default.TraitTypeContainingMethod(_1287_resolvedType, _pat_let_tv194);
            }
          }
          if (unmatched63) {
            unmatched63 = false;
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
          throw new System.Exception("unexpected control point");
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source64 = _1286_res;
        bool unmatched64 = true;
        if (unmatched64) {
          if (_source64.is_Some) {
            unmatched64 = false;
            return _1286_res;
          }
        }
        if (unmatched64) {
          unmatched64 = false;
          return DCOMP.__default.TraitTypeContainingMethodAux((_pat_let_tv195).Drop(BigInteger.One), _pat_let_tv196);
        }
        throw new System.Exception("unexpected control point");
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethod(DAST._IResolvedType r, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DAST._IResolvedType _let_tmp_rhs53 = r;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1288_path = _let_tmp_rhs53.dtor_path;
      Dafny.ISequence<DAST._IType> _1289_typeArgs = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedTypeBase _1290_kind = _let_tmp_rhs53.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1291_attributes = _let_tmp_rhs53.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1292_properMethods = _let_tmp_rhs53.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1293_extendedTypes = _let_tmp_rhs53.dtor_extendedTypes;
      if ((_1292_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1293_extendedTypes, dafnyName);
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
      Dafny.ISequence<Dafny.Rune> _1294___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1294___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((s).Select(BigInteger.Zero)) == (new Dafny.Rune(' '))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1294___accumulator, s);
      } else {
        _1294___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1294___accumulator, ((((s).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")) : (Dafny.Sequence<Dafny.Rune>.FromElements((s).Select(BigInteger.Zero)))));
        Dafny.ISequence<Dafny.Rune> _in128 = (s).Drop(BigInteger.One);
        s = _in128;
        goto TAIL_CALL_START;
      }
    }
    public static DCOMP._IExternAttribute ExtractExtern(Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DCOMP._IExternAttribute res = DCOMP.ExternAttribute.Default();
      BigInteger _hi5 = new BigInteger((attributes).Count);
      for (BigInteger _1295_i = BigInteger.Zero; _1295_i < _hi5; _1295_i++) {
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _1296_attr;
        _1296_attr = DCOMP.__default.OptExtern((attributes).Select(_1295_i), dafnyName);
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _source65 = _1296_attr;
        bool unmatched65 = true;
        if (unmatched65) {
          if (_source65.is_Some) {
            DCOMP._IExternAttribute _1297_n = _source65.dtor_value;
            unmatched65 = false;
            res = _1297_n;
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
      DCOMP._IEnvironment _1298_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1299_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll7 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_8 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1300_k = (Dafny.ISequence<Dafny.Rune>)_compr_8;
          if (((this).dtor_types).Contains(_1300_k)) {
            _coll7.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_1300_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_1300_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll7);
      }))();
      return DCOMP.Environment.create((_1298_dt__update__tmp_h0).dtor_names, _1299_dt__update_htypes_h0);
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
      BigInteger _1301_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1301_indexInEnv), ((this).dtor_names).Drop((_1301_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
    public RAST._IMod GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      RAST._IMod s = RAST.Mod.Default();
      Dafny.ISequence<Dafny.Rune> _1302_modName;
      _1302_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1302_modName);
      } else {
        DCOMP._IExternAttribute _1303_optExtern;
        _1303_optExtern = DCOMP.__default.ExtractExternMod(mod);
        Dafny.ISequence<RAST._IModDecl> _1304_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1304_body = _out15;
        if ((_1303_optExtern).is_SimpleExtern) {
          if ((mod).dtor_requiresExterns) {
            _1304_body = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (((RAST.__default.crate).MSel(DCOMP.COMP.DAFNY__EXTERN__MODULE)).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1303_optExtern).dtor_overrideName))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))), _1304_body);
          }
        } else if ((_1303_optExtern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Externs on modules can only have 1 string argument"));
        } else if ((_1303_optExtern).is_UnsupportedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some((_1303_optExtern).dtor_reason);
        }
        s = RAST.Mod.create_Mod(_1302_modName, _1304_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi6 = new BigInteger((body).Count);
      for (BigInteger _1305_i = BigInteger.Zero; _1305_i < _hi6; _1305_i++) {
        Dafny.ISequence<RAST._IModDecl> _1306_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source66 = (body).Select(_1305_i);
        bool unmatched66 = true;
        if (unmatched66) {
          if (_source66.is_Module) {
            DAST._IModule _1307_m = _source66.dtor_Module_a0;
            unmatched66 = false;
            RAST._IMod _1308_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1307_m, containingPath);
            _1308_mm = _out16;
            _1306_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1308_mm));
          }
        }
        if (unmatched66) {
          if (_source66.is_Class) {
            DAST._IClass _1309_c = _source66.dtor_Class_a0;
            unmatched66 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1309_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1309_c).dtor_name)));
            _1306_generated = _out17;
          }
        }
        if (unmatched66) {
          if (_source66.is_Trait) {
            DAST._ITrait _1310_t = _source66.dtor_Trait_a0;
            unmatched66 = false;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenTrait(_1310_t, containingPath);
            _1306_generated = _out18;
          }
        }
        if (unmatched66) {
          if (_source66.is_Newtype) {
            DAST._INewtype _1311_n = _source66.dtor_Newtype_a0;
            unmatched66 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1311_n);
            _1306_generated = _out19;
          }
        }
        if (unmatched66) {
          if (_source66.is_SynonymType) {
            DAST._ISynonymType _1312_s = _source66.dtor_SynonymType_a0;
            unmatched66 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1312_s);
            _1306_generated = _out20;
          }
        }
        if (unmatched66) {
          DAST._IDatatype _1313_d = _source66.dtor_Datatype_a0;
          unmatched66 = false;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1313_d);
          _1306_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1306_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1314_genTpConstraint;
      _1314_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1314_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1314_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1314_genTpConstraint);
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
        for (BigInteger _1315_tpI = BigInteger.Zero; _1315_tpI < _hi7; _1315_tpI++) {
          DAST._ITypeArgDecl _1316_tp;
          _1316_tp = (@params).Select(_1315_tpI);
          DAST._IType _1317_typeArg;
          RAST._ITypeParamDecl _1318_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1316_tp, out _out22, out _out23);
          _1317_typeArg = _out22;
          _1318_typeParam = _out23;
          RAST._IType _1319_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1317_typeArg, DCOMP.GenTypeContext.@default());
          _1319_rType = _out24;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1317_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1319_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1318_typeParam));
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
      Dafny.ISequence<DAST._IType> _1320_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1321_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1322_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1323_whereConstraints;
      Dafny.ISequence<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1320_typeParamsSeq = _out25;
      _1321_rTypeParams = _out26;
      _1322_rTypeParamsDecls = _out27;
      _1323_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1324_constrainedTypeParams;
      _1324_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1322_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1325_fields;
      _1325_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1326_fieldInits;
      _1326_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi8 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1327_fieldI = BigInteger.Zero; _1327_fieldI < _hi8; _1327_fieldI++) {
        DAST._IField _1328_field;
        _1328_field = ((c).dtor_fields).Select(_1327_fieldI);
        RAST._IType _1329_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1328_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1329_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1330_fieldRustName;
        _1330_fieldRustName = DCOMP.__default.escapeVar(((_1328_field).dtor_formal).dtor_name);
        _1325_fields = Dafny.Sequence<RAST._IField>.Concat(_1325_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1330_fieldRustName, _1329_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source67 = (_1328_field).dtor_defaultValue;
        bool unmatched67 = true;
        if (unmatched67) {
          if (_source67.is_Some) {
            DAST._IExpression _1331_e = _source67.dtor_value;
            unmatched67 = false;
            {
              RAST._IExpr _1332_expr;
              DCOMP._IOwnership _1333___v50;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1334___v51;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1331_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1332_expr = _out30;
              _1333___v50 = _out31;
              _1334___v51 = _out32;
              _1326_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1326_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1330_fieldRustName, _1332_expr)));
            }
          }
        }
        if (unmatched67) {
          unmatched67 = false;
          {
            RAST._IExpr _1335_default;
            _1335_default = RAST.__default.std__Default__default;
            if ((_1329_fieldType).IsObjectOrPointer()) {
              _1335_default = (_1329_fieldType).ToNullExpr();
            }
            _1326_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1326_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1330_fieldRustName, _1335_default)));
          }
        }
      }
      BigInteger _hi9 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1336_typeParamI = BigInteger.Zero; _1336_typeParamI < _hi9; _1336_typeParamI++) {
        DAST._IType _1337_typeArg;
        RAST._ITypeParamDecl _1338_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1336_typeParamI), out _out33, out _out34);
        _1337_typeArg = _out33;
        _1338_typeParam = _out34;
        RAST._IType _1339_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1337_typeArg, DCOMP.GenTypeContext.@default());
        _1339_rTypeArg = _out35;
        _1325_fields = Dafny.Sequence<RAST._IField>.Concat(_1325_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1336_typeParamI)), RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1339_rTypeArg))))));
        _1326_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1326_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1336_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      DCOMP._IExternAttribute _1340_extern;
      _1340_extern = DCOMP.__default.ExtractExtern((c).dtor_attributes, (c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _1341_className = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((_1340_extern).is_SimpleExtern) {
        _1341_className = (_1340_extern).dtor_overrideName;
      } else {
        _1341_className = DCOMP.__default.escapeName((c).dtor_name);
        if ((_1340_extern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multi-argument externs not supported for classes yet"));
        }
      }
      RAST._IStruct _1342_struct;
      _1342_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1341_className, _1322_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1325_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_1340_extern).is_NoExtern) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1342_struct)));
      }
      Dafny.ISequence<RAST._IImplMember> _1343_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1344_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1320_typeParamsSeq, out _out36, out _out37);
      _1343_implBody = _out36;
      _1344_traitBodies = _out37;
      if (((_1340_extern).is_NoExtern) && (!(_1341_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default")))) {
        _1343_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.__default.SelfOwned)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel((this).allocate)).AsExpr()).ApplyType1(RAST.__default.SelfOwned)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1343_implBody);
      }
      RAST._IType _1345_selfTypeForImpl = RAST.Type.Default();
      if (((_1340_extern).is_NoExtern) || ((_1340_extern).is_UnsupportedExtern)) {
        _1345_selfTypeForImpl = RAST.Type.create_TIdentifier(_1341_className);
      } else if ((_1340_extern).is_AdvancedExtern) {
        _1345_selfTypeForImpl = (((RAST.__default.crate).MSel((_1340_extern).dtor_enclosingModule)).MSel((_1340_extern).dtor_overrideName)).AsType();
      } else if ((_1340_extern).is_SimpleExtern) {
        _1345_selfTypeForImpl = RAST.Type.create_TIdentifier((_1340_extern).dtor_overrideName);
      }
      if ((new BigInteger((_1343_implBody).Count)).Sign == 1) {
        RAST._IImpl _1346_i;
        _1346_i = RAST.Impl.create_Impl(_1322_rTypeParamsDecls, RAST.Type.create_TypeApp(_1345_selfTypeForImpl, _1321_rTypeParams), _1323_whereConstraints, _1343_implBody);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1346_i)));
      }
      RAST._IType _1347_genSelfPath;
      RAST._IType _out38;
      _out38 = DCOMP.COMP.GenPathType(path);
      _1347_genSelfPath = _out38;
      if (!(_1341_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1322_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(RAST.__default.AnyTrait))), RAST.Type.create_TypeApp(_1347_genSelfPath, _1321_rTypeParams), _1323_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(RAST.__default.AnyTrait)))))))));
      }
      Dafny.ISequence<DAST._IType> _1348_superClasses;
      _1348_superClasses = (((_1341_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) ? (Dafny.Sequence<DAST._IType>.FromElements()) : ((c).dtor_superClasses));
      BigInteger _hi10 = new BigInteger((_1348_superClasses).Count);
      for (BigInteger _1349_i = BigInteger.Zero; _1349_i < _hi10; _1349_i++) {
        DAST._IType _1350_superClass;
        _1350_superClass = (_1348_superClasses).Select(_1349_i);
        DAST._IType _source68 = _1350_superClass;
        bool unmatched68 = true;
        if (unmatched68) {
          if (_source68.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source68.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1351_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1352_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1353_properMethods = resolved0.dtor_properMethods;
              unmatched68 = false;
              {
                RAST._IType _1354_pathStr;
                RAST._IType _out39;
                _out39 = DCOMP.COMP.GenPathType(_1351_traitPath);
                _1354_pathStr = _out39;
                Dafny.ISequence<RAST._IType> _1355_typeArgs;
                Dafny.ISequence<RAST._IType> _out40;
                _out40 = (this).GenTypeArgs(_1352_typeArgs, DCOMP.GenTypeContext.@default());
                _1355_typeArgs = _out40;
                Dafny.ISequence<RAST._IImplMember> _1356_body;
                _1356_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1344_traitBodies).Contains(_1351_traitPath)) {
                  _1356_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1344_traitBodies,_1351_traitPath);
                }
                RAST._IType _1357_traitType;
                _1357_traitType = RAST.Type.create_TypeApp(_1354_pathStr, _1355_typeArgs);
                if (!((_1340_extern).is_NoExtern)) {
                  if (((new BigInteger((_1356_body).Count)).Sign == 0) && ((new BigInteger((_1353_properMethods).Count)).Sign != 0)) {
                    goto continue_0;
                  }
                  if ((new BigInteger((_1356_body).Count)) != (new BigInteger((_1353_properMethods).Count))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: In the class "), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(path, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1358_s) => {
  return ((_1358_s));
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", some proper methods of ")), (_1357_traitType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" are marked {:extern} and some are not.")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" For the Rust compiler, please make all methods (")), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_1353_properMethods, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1359_s) => {
  return (_1359_s);
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")  bodiless and mark as {:extern} and implement them in a Rust file, ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("or mark none of them as {:extern} and implement them in Dafny. ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.")));
                  }
                }
                RAST._IModDecl _1360_x;
                _1360_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1322_rTypeParamsDecls, _1357_traitType, RAST.Type.create_TypeApp(_1347_genSelfPath, _1321_rTypeParams), _1323_whereConstraints, _1356_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1360_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1322_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1357_traitType))), RAST.Type.create_TypeApp(_1347_genSelfPath, _1321_rTypeParams), _1323_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1357_traitType)))))))));
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
      Dafny.ISequence<DAST._IType> _1361_typeParamsSeq;
      _1361_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1362_typeParamDecls;
      _1362_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1363_typeParams;
      _1363_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi11 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1364_tpI = BigInteger.Zero; _1364_tpI < _hi11; _1364_tpI++) {
          DAST._ITypeArgDecl _1365_tp;
          _1365_tp = ((t).dtor_typeParams).Select(_1364_tpI);
          DAST._IType _1366_typeArg;
          RAST._ITypeParamDecl _1367_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1365_tp, out _out41, out _out42);
          _1366_typeArg = _out41;
          _1367_typeParamDecl = _out42;
          _1361_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1361_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1366_typeArg));
          _1362_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1362_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1367_typeParamDecl));
          RAST._IType _1368_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1366_typeArg, DCOMP.GenTypeContext.@default());
          _1368_typeParam = _out43;
          _1363_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1363_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1368_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1369_fullPath;
      _1369_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1370_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1371___v55;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1369_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1361_typeParamsSeq, out _out44, out _out45);
      _1370_implBody = _out44;
      _1371___v55 = _out45;
      Dafny.ISequence<RAST._IType> _1372_parents;
      _1372_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi12 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1373_i = BigInteger.Zero; _1373_i < _hi12; _1373_i++) {
        RAST._IType _1374_tpe;
        RAST._IType _out46;
        _out46 = (this).GenType(((t).dtor_parents).Select(_1373_i), DCOMP.GenTypeContext.ForTraitParents());
        _1374_tpe = _out46;
        _1372_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1372_parents, Dafny.Sequence<RAST._IType>.FromElements(_1374_tpe)), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply1(RAST.Type.create_DynType(_1374_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1362_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1363_typeParams), _1372_parents, _1370_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1375_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1376_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1377_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1378_whereConstraints;
      Dafny.ISequence<DAST._IType> _out47;
      Dafny.ISequence<RAST._IType> _out48;
      Dafny.ISequence<RAST._ITypeParamDecl> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1375_typeParamsSeq = _out47;
      _1376_rTypeParams = _out48;
      _1377_rTypeParamsDecls = _out49;
      _1378_whereConstraints = _out50;
      Dafny.ISequence<Dafny.Rune> _1379_constrainedTypeParams;
      _1379_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1377_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1380_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source69 = DCOMP.COMP.NewtypeRangeToRustType((c).dtor_range);
      bool unmatched69 = true;
      if (unmatched69) {
        if (_source69.is_Some) {
          RAST._IType _1381_v = _source69.dtor_value;
          unmatched69 = false;
          _1380_underlyingType = _1381_v;
        }
      }
      if (unmatched69) {
        unmatched69 = false;
        RAST._IType _out51;
        _out51 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1380_underlyingType = _out51;
      }
      DAST._IType _1382_resultingType;
      _1382_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1383_newtypeName;
      _1383_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1383_newtypeName, _1377_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1380_underlyingType))))));
      RAST._IExpr _1384_fnBody;
      _1384_fnBody = RAST.Expr.create_Identifier(_1383_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source70 = (c).dtor_witnessExpr;
      bool unmatched70 = true;
      if (unmatched70) {
        if (_source70.is_Some) {
          DAST._IExpression _1385_e = _source70.dtor_value;
          unmatched70 = false;
          {
            DAST._IExpression _1386_e;
            _1386_e = ((object.Equals((c).dtor_base, _1382_resultingType)) ? (_1385_e) : (DAST.Expression.create_Convert(_1385_e, (c).dtor_base, _1382_resultingType)));
            RAST._IExpr _1387_eStr;
            DCOMP._IOwnership _1388___v56;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1389___v57;
            RAST._IExpr _out52;
            DCOMP._IOwnership _out53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out54;
            (this).GenExpr(_1386_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out52, out _out53, out _out54);
            _1387_eStr = _out52;
            _1388___v56 = _out53;
            _1389___v57 = _out54;
            _1384_fnBody = (_1384_fnBody).Apply1(_1387_eStr);
          }
        }
      }
      if (unmatched70) {
        unmatched70 = false;
        {
          _1384_fnBody = (_1384_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1390_body;
      _1390_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1384_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source71 = (c).dtor_constraint;
      bool unmatched71 = true;
      if (unmatched71) {
        if (_source71.is_None) {
          unmatched71 = false;
        }
      }
      if (unmatched71) {
        DAST._INewtypeConstraint value8 = _source71.dtor_value;
        DAST._IFormal _1391_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1392_constraintStmts = value8.dtor_constraintStmts;
        unmatched71 = false;
        RAST._IExpr _1393_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1394___v58;
        DCOMP._IEnvironment _1395_newEnv;
        RAST._IExpr _out55;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out56;
        DCOMP._IEnvironment _out57;
        (this).GenStmts(_1392_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out55, out _out56, out _out57);
        _1393_rStmts = _out55;
        _1394___v58 = _out56;
        _1395_newEnv = _out57;
        Dafny.ISequence<RAST._IFormal> _1396_rFormals;
        Dafny.ISequence<RAST._IFormal> _out58;
        _out58 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1391_formal), false);
        _1396_rFormals = _out58;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1377_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1383_newtypeName), _1376_rTypeParams), _1378_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1396_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1393_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1377_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1383_newtypeName), _1376_rTypeParams), _1378_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1390_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1377_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1383_newtypeName), _1376_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1377_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1383_newtypeName), _1376_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1380_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(((RAST.Path.create_Self()).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))).AsType())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1397_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1398_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1399_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1400_whereConstraints;
      Dafny.ISequence<DAST._IType> _out59;
      Dafny.ISequence<RAST._IType> _out60;
      Dafny.ISequence<RAST._ITypeParamDecl> _out61;
      Dafny.ISequence<Dafny.Rune> _out62;
      (this).GenTypeParameters((c).dtor_typeParams, out _out59, out _out60, out _out61, out _out62);
      _1397_typeParamsSeq = _out59;
      _1398_rTypeParams = _out60;
      _1399_rTypeParamsDecls = _out61;
      _1400_whereConstraints = _out62;
      Dafny.ISequence<Dafny.Rune> _1401_synonymTypeName;
      _1401_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1402_resultingType;
      RAST._IType _out63;
      _out63 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1402_resultingType = _out63;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1401_synonymTypeName, _1399_rTypeParamsDecls, _1402_resultingType)));
      Dafny.ISequence<RAST._ITypeParamDecl> _1403_defaultConstrainedTypeParams;
      _1403_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1399_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Std.Wrappers._IOption<DAST._IExpression> _source72 = (c).dtor_witnessExpr;
      bool unmatched72 = true;
      if (unmatched72) {
        if (_source72.is_Some) {
          DAST._IExpression _1404_e = _source72.dtor_value;
          unmatched72 = false;
          {
            RAST._IExpr _1405_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1406___v59;
            DCOMP._IEnvironment _1407_newEnv;
            RAST._IExpr _out64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out65;
            DCOMP._IEnvironment _out66;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out64, out _out65, out _out66);
            _1405_rStmts = _out64;
            _1406___v59 = _out65;
            _1407_newEnv = _out66;
            RAST._IExpr _1408_rExpr;
            DCOMP._IOwnership _1409___v60;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1410___v61;
            RAST._IExpr _out67;
            DCOMP._IOwnership _out68;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out69;
            (this).GenExpr(_1404_e, DCOMP.SelfInfo.create_NoSelf(), _1407_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out67, out _out68, out _out69);
            _1408_rExpr = _out67;
            _1409___v60 = _out68;
            _1410___v61 = _out69;
            Dafny.ISequence<Dafny.Rune> _1411_constantName;
            _1411_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1411_constantName, _1403_defaultConstrainedTypeParams, Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1402_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1405_rStmts).Then(_1408_rExpr)))))));
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
          Dafny.ISequence<DAST._IType> _1412_ts = _source73.dtor_Tuple_a0;
          unmatched73 = false;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1413_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1413_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1414_t = (DAST._IType)_forall_var_5;
            return !((_1413_ts).Contains(_1414_t)) || ((this).TypeIsEq(_1414_t));
          }))))(_1412_ts);
        }
      }
      if (unmatched73) {
        if (_source73.is_Array) {
          DAST._IType _1415_t = _source73.dtor_element;
          unmatched73 = false;
          return (this).TypeIsEq(_1415_t);
        }
      }
      if (unmatched73) {
        if (_source73.is_Seq) {
          DAST._IType _1416_t = _source73.dtor_element;
          unmatched73 = false;
          return (this).TypeIsEq(_1416_t);
        }
      }
      if (unmatched73) {
        if (_source73.is_Set) {
          DAST._IType _1417_t = _source73.dtor_element;
          unmatched73 = false;
          return (this).TypeIsEq(_1417_t);
        }
      }
      if (unmatched73) {
        if (_source73.is_Multiset) {
          DAST._IType _1418_t = _source73.dtor_element;
          unmatched73 = false;
          return (this).TypeIsEq(_1418_t);
        }
      }
      if (unmatched73) {
        if (_source73.is_Map) {
          DAST._IType _1419_k = _source73.dtor_key;
          DAST._IType _1420_v = _source73.dtor_value;
          unmatched73 = false;
          return ((this).TypeIsEq(_1419_k)) && ((this).TypeIsEq(_1420_v));
        }
      }
      if (unmatched73) {
        if (_source73.is_SetBuilder) {
          DAST._IType _1421_t = _source73.dtor_element;
          unmatched73 = false;
          return (this).TypeIsEq(_1421_t);
        }
      }
      if (unmatched73) {
        if (_source73.is_MapBuilder) {
          DAST._IType _1422_k = _source73.dtor_key;
          DAST._IType _1423_v = _source73.dtor_value;
          unmatched73 = false;
          return ((this).TypeIsEq(_1422_k)) && ((this).TypeIsEq(_1423_v));
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
          Dafny.ISequence<Dafny.Rune> _1424_i = _source73.dtor_TypeArg_a0;
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
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1425_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1425_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1426_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1426_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1427_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1425_c).dtor_ctors).Contains(_1426_ctor)) && (((_1426_ctor).dtor_args).Contains(_1427_arg))) || ((this).TypeIsEq(((_1427_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1428_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1429_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1430_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1431_whereConstraints;
      Dafny.ISequence<DAST._IType> _out70;
      Dafny.ISequence<RAST._IType> _out71;
      Dafny.ISequence<RAST._ITypeParamDecl> _out72;
      Dafny.ISequence<Dafny.Rune> _out73;
      (this).GenTypeParameters((c).dtor_typeParams, out _out70, out _out71, out _out72, out _out73);
      _1428_typeParamsSeq = _out70;
      _1429_rTypeParams = _out71;
      _1430_rTypeParamsDecls = _out72;
      _1431_whereConstraints = _out73;
      Dafny.ISequence<Dafny.Rune> _1432_datatypeName;
      _1432_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1433_ctors;
      _1433_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _1434_variances;
      _1434_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_1435_typeParamDecl) => {
        return (_1435_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1436_i = BigInteger.Zero; _1436_i < _hi13; _1436_i++) {
        DAST._IDatatypeCtor _1437_ctor;
        _1437_ctor = ((c).dtor_ctors).Select(_1436_i);
        Dafny.ISequence<RAST._IField> _1438_ctorArgs;
        _1438_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1439_isNumeric;
        _1439_isNumeric = false;
        BigInteger _hi14 = new BigInteger(((_1437_ctor).dtor_args).Count);
        for (BigInteger _1440_j = BigInteger.Zero; _1440_j < _hi14; _1440_j++) {
          DAST._IDatatypeDtor _1441_dtor;
          _1441_dtor = ((_1437_ctor).dtor_args).Select(_1440_j);
          RAST._IType _1442_formalType;
          RAST._IType _out74;
          _out74 = (this).GenType(((_1441_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1442_formalType = _out74;
          Dafny.ISequence<Dafny.Rune> _1443_formalName;
          _1443_formalName = DCOMP.__default.escapeVar(((_1441_dtor).dtor_formal).dtor_name);
          if (((_1440_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1443_formalName))) {
            _1439_isNumeric = true;
          }
          if ((((_1440_j).Sign != 0) && (_1439_isNumeric)) && (!(Std.Strings.__default.OfNat(_1440_j)).Equals(_1443_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1443_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1440_j)));
            _1439_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1438_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1438_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1443_formalName, RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1442_formalType))))));
          } else {
            _1438_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1438_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1443_formalName, _1442_formalType))));
          }
        }
        RAST._IFields _1444_namedFields;
        _1444_namedFields = RAST.Fields.create_NamedFields(_1438_ctorArgs);
        if (_1439_isNumeric) {
          _1444_namedFields = (_1444_namedFields).ToNamelessFields();
        }
        _1433_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1433_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1437_ctor).dtor_name), _1444_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1445_selfPath;
      _1445_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1446_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1447_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out75;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out76;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1445_selfPath, _1428_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1434_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1428_typeParamsSeq, out _out75, out _out76);
      _1446_implBodyRaw = _out75;
      _1447_traitBodies = _out76;
      Dafny.ISequence<RAST._IImplMember> _1448_implBody;
      _1448_implBody = _1446_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1449_emittedFields;
      _1449_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi15 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1450_i = BigInteger.Zero; _1450_i < _hi15; _1450_i++) {
        DAST._IDatatypeCtor _1451_ctor;
        _1451_ctor = ((c).dtor_ctors).Select(_1450_i);
        BigInteger _hi16 = new BigInteger(((_1451_ctor).dtor_args).Count);
        for (BigInteger _1452_j = BigInteger.Zero; _1452_j < _hi16; _1452_j++) {
          DAST._IDatatypeDtor _1453_dtor;
          _1453_dtor = ((_1451_ctor).dtor_args).Select(_1452_j);
          Dafny.ISequence<Dafny.Rune> _1454_callName;
          _1454_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1453_dtor).dtor_callName, DCOMP.__default.escapeVar(((_1453_dtor).dtor_formal).dtor_name));
          if (!((_1449_emittedFields).Contains(_1454_callName))) {
            _1449_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1449_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1454_callName));
            RAST._IType _1455_formalType;
            RAST._IType _out77;
            _out77 = (this).GenType(((_1453_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1455_formalType = _out77;
            Dafny.ISequence<RAST._IMatchCase> _1456_cases;
            _1456_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi17 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1457_k = BigInteger.Zero; _1457_k < _hi17; _1457_k++) {
              DAST._IDatatypeCtor _1458_ctor2;
              _1458_ctor2 = ((c).dtor_ctors).Select(_1457_k);
              Dafny.ISequence<Dafny.Rune> _1459_pattern;
              _1459_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1432_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1458_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1460_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1461_hasMatchingField;
              _1461_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1462_patternInner;
              _1462_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1463_isNumeric;
              _1463_isNumeric = false;
              BigInteger _hi18 = new BigInteger(((_1458_ctor2).dtor_args).Count);
              for (BigInteger _1464_l = BigInteger.Zero; _1464_l < _hi18; _1464_l++) {
                DAST._IDatatypeDtor _1465_dtor2;
                _1465_dtor2 = ((_1458_ctor2).dtor_args).Select(_1464_l);
                Dafny.ISequence<Dafny.Rune> _1466_patternName;
                _1466_patternName = DCOMP.__default.escapeVar(((_1465_dtor2).dtor_formal).dtor_name);
                if (((_1464_l).Sign == 0) && ((_1466_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1463_isNumeric = true;
                }
                if (_1463_isNumeric) {
                  _1466_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1465_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1464_l)));
                }
                if (object.Equals(((_1453_dtor).dtor_formal).dtor_name, ((_1465_dtor2).dtor_formal).dtor_name)) {
                  _1461_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1466_patternName);
                }
                _1462_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1462_patternInner, _1466_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1463_isNumeric) {
                _1459_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1459_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1462_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1459_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1459_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1462_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1461_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1460_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1461_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1460_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1461_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1460_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _1467_ctorMatch;
              _1467_ctorMatch = RAST.MatchCase.create(_1459_pattern, RAST.Expr.create_RawExpr(_1460_rhs));
              _1456_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1456_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1467_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1456_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1456_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1432_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _1468_methodBody;
            _1468_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1456_cases);
            _1448_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1448_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1454_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1455_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1468_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1469_coerceTypes;
      _1469_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1470_rCoerceTypeParams;
      _1470_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1471_coerceArguments;
      _1471_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1472_coerceMap;
      _1472_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1473_rCoerceMap;
      _1473_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1474_coerceMapToArg;
      _1474_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1475_types;
        _1475_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi19 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1476_typeI = BigInteger.Zero; _1476_typeI < _hi19; _1476_typeI++) {
          DAST._ITypeArgDecl _1477_typeParam;
          _1477_typeParam = ((c).dtor_typeParams).Select(_1476_typeI);
          DAST._IType _1478_typeArg;
          RAST._ITypeParamDecl _1479_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(_1477_typeParam, out _out78, out _out79);
          _1478_typeArg = _out78;
          _1479_rTypeParamDecl = _out79;
          RAST._IType _1480_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1478_typeArg, DCOMP.GenTypeContext.@default());
          _1480_rTypeArg = _out80;
          _1475_types = Dafny.Sequence<RAST._IType>.Concat(_1475_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1480_rTypeArg))));
          if (((_1476_typeI) < (new BigInteger((_1434_variances).Count))) && (((_1434_variances).Select(_1476_typeI)).is_Nonvariant)) {
            _1469_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1469_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1480_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1481_coerceTypeParam;
          _1481_coerceTypeParam = Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_1477_typeParam, _pat_let18_0 => Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_pat_let18_0, _1482_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1476_typeI)), _pat_let19_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(_pat_let19_0, _1483_dt__update_hname_h0 => DAST.TypeArgDecl.create(_1483_dt__update_hname_h0, (_1482_dt__update__tmp_h0).dtor_bounds, (_1482_dt__update__tmp_h0).dtor_variance)))));
          DAST._IType _1484_coerceTypeArg;
          RAST._ITypeParamDecl _1485_rCoerceTypeParamDecl;
          DAST._IType _out81;
          RAST._ITypeParamDecl _out82;
          (this).GenTypeParam(_1481_coerceTypeParam, out _out81, out _out82);
          _1484_coerceTypeArg = _out81;
          _1485_rCoerceTypeParamDecl = _out82;
          _1472_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1472_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1478_typeArg, _1484_coerceTypeArg)));
          RAST._IType _1486_rCoerceType;
          RAST._IType _out83;
          _out83 = (this).GenType(_1484_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1486_rCoerceType = _out83;
          _1473_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1473_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1480_rTypeArg, _1486_rCoerceType)));
          _1469_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1469_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1486_rCoerceType));
          _1470_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1470_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1485_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1487_coerceFormal;
          _1487_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1476_typeI));
          _1474_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1474_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1480_rTypeArg, _1486_rCoerceType), (RAST.Expr.create_Identifier(_1487_coerceFormal)).Clone())));
          _1471_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1471_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1487_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1480_rTypeArg), _1486_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        _1433_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1433_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1488_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1488_tpe);
})), _1475_types)))));
      }
      bool _1489_cIsEq;
      _1489_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1489_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1432_datatypeName, _1430_rTypeParamsDecls, _1433_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1430_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1432_datatypeName), _1429_rTypeParams), _1431_whereConstraints, _1448_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1490_printImplBodyCases;
      _1490_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1491_hashImplBodyCases;
      _1491_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1492_coerceImplBodyCases;
      _1492_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi20 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1493_i = BigInteger.Zero; _1493_i < _hi20; _1493_i++) {
        DAST._IDatatypeCtor _1494_ctor;
        _1494_ctor = ((c).dtor_ctors).Select(_1493_i);
        Dafny.ISequence<Dafny.Rune> _1495_ctorMatch;
        _1495_ctorMatch = DCOMP.__default.escapeName((_1494_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1496_modulePrefix;
        _1496_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1497_ctorName;
        _1497_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1496_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1494_ctor).dtor_name));
        if (((new BigInteger((_1497_ctorName).Count)) >= (new BigInteger(13))) && (((_1497_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1497_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1498_printRhs;
        _1498_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1497_ctorName), (((_1494_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1499_hashRhs;
        _1499_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1500_coerceRhsArgs;
        _1500_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1501_isNumeric;
        _1501_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1502_ctorMatchInner;
        _1502_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi21 = new BigInteger(((_1494_ctor).dtor_args).Count);
        for (BigInteger _1503_j = BigInteger.Zero; _1503_j < _hi21; _1503_j++) {
          DAST._IDatatypeDtor _1504_dtor;
          _1504_dtor = ((_1494_ctor).dtor_args).Select(_1503_j);
          Dafny.ISequence<Dafny.Rune> _1505_patternName;
          _1505_patternName = DCOMP.__default.escapeVar(((_1504_dtor).dtor_formal).dtor_name);
          DAST._IType _1506_formalType;
          _1506_formalType = ((_1504_dtor).dtor_formal).dtor_typ;
          if (((_1503_j).Sign == 0) && ((_1505_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1501_isNumeric = true;
          }
          if (_1501_isNumeric) {
            _1505_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1504_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1503_j)));
          }
          _1499_hashRhs = (((_1506_formalType).is_Arrow) ? ((_1499_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))) : ((_1499_hashRhs).Then((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1505_patternName), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state")))))));
          _1502_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1502_ctorMatchInner, _1505_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1503_j).Sign == 1) {
            _1498_printRhs = (_1498_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1498_printRhs = (_1498_printRhs).Then(RAST.Expr.create_RawExpr((((_1506_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1505_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1507_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1508_formalTpe;
          RAST._IType _out84;
          _out84 = (this).GenType(_1506_formalType, DCOMP.GenTypeContext.@default());
          _1508_formalTpe = _out84;
          DAST._IType _1509_newFormalType;
          _1509_newFormalType = (_1506_formalType).Replace(_1472_coerceMap);
          RAST._IType _1510_newFormalTpe;
          _1510_newFormalTpe = (_1508_formalTpe).ReplaceMap(_1473_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1511_upcastConverter;
          _1511_upcastConverter = (this).UpcastConversionLambda(_1506_formalType, _1508_formalTpe, _1509_newFormalType, _1510_newFormalTpe, _1474_coerceMapToArg);
          if ((_1511_upcastConverter).is_Success) {
            RAST._IExpr _1512_coercionFunction;
            _1512_coercionFunction = (_1511_upcastConverter).dtor_value;
            _1507_coerceRhsArg = (_1512_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1505_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1503_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1432_datatypeName));
            _1507_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1500_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1500_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1505_patternName, _1507_coerceRhsArg)));
        }
        RAST._IExpr _1513_coerceRhs;
        _1513_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1432_datatypeName)).FSel(DCOMP.__default.escapeName((_1494_ctor).dtor_name)), _1500_coerceRhsArgs);
        if (_1501_isNumeric) {
          _1495_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1495_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1502_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1495_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1495_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1502_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1494_ctor).dtor_hasAnyArgs) {
          _1498_printRhs = (_1498_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1498_printRhs = (_1498_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1490_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1490_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1432_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1495_ctorMatch), RAST.Expr.create_Block(_1498_printRhs))));
        _1491_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1491_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1432_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1495_ctorMatch), RAST.Expr.create_Block(_1499_hashRhs))));
        _1492_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1492_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1432_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1495_ctorMatch), RAST.Expr.create_Block(_1513_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1514_extraCases;
        _1514_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1432_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _1490_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1490_printImplBodyCases, _1514_extraCases);
        _1491_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1491_hashImplBodyCases, _1514_extraCases);
        _1492_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1492_coerceImplBodyCases, _1514_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1515_defaultConstrainedTypeParams;
      _1515_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1430_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1516_rTypeParamsDeclsWithEq;
      _1516_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1430_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1517_rTypeParamsDeclsWithHash;
      _1517_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1430_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1518_printImplBody;
      _1518_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1490_printImplBodyCases);
      RAST._IExpr _1519_hashImplBody;
      _1519_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1491_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1430_rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug"))).AsType(), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1432_datatypeName), _1429_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType()))), Std.Wrappers.Option<RAST._IType>.create_Some((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Result"))).AsType()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1430_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1432_datatypeName), _1429_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType())), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1518_printImplBody))))))));
      if ((new BigInteger((_1470_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1520_coerceImplBody;
        _1520_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1492_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1430_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1432_datatypeName), _1429_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1470_rCoerceTypeParams, _1471_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1432_datatypeName), _1429_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1432_datatypeName), _1469_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.__default.SelfOwned)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1432_datatypeName), _1469_coerceTypes)), _1520_coerceImplBody))))))))));
      }
      if (_1489_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1516_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1432_datatypeName), _1429_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1517_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1432_datatypeName), _1429_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))).AsType()))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1519_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1521_structName;
        _1521_structName = (RAST.Expr.create_Identifier(_1432_datatypeName)).FSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1522_structAssignments;
        _1522_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi22 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1523_i = BigInteger.Zero; _1523_i < _hi22; _1523_i++) {
          DAST._IDatatypeDtor _1524_dtor;
          _1524_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1523_i);
          _1522_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1522_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(((_1524_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1525_defaultConstrainedTypeParams;
        _1525_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1430_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1526_fullType;
        _1526_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1432_datatypeName), _1429_rTypeParams);
        if (_1489_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1525_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1526_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1526_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1521_structName, _1522_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1430_rTypeParamsDecls, ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).AsType()).Apply1(_1526_fullType), RAST.Type.create_Borrowed(_1526_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        for (BigInteger _1527_i = BigInteger.Zero; _1527_i < _hi23; _1527_i++) {
          Dafny.ISequence<Dafny.Rune> _1528_id;
          _1528_id = ((p).Select(_1527_i));
          r = (r).MSel(((escape) ? (DCOMP.__default.escapeName(_1528_id)) : (DCOMP.__default.ReplaceDotByDoubleColon((_1528_id)))));
        }
      }
      return r;
    }
    public static RAST._IType GenPathType(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IType t = RAST.Type.Default();
      RAST._IPath _1529_p;
      RAST._IPath _out85;
      _out85 = DCOMP.COMP.GenPath(p, true);
      _1529_p = _out85;
      t = (_1529_p).AsType();
      return t;
    }
    public static RAST._IExpr GenPathExpr(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p, bool escape)
    {
      RAST._IExpr e = RAST.Expr.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        e = RAST.__default.self;
        return e;
      }
      RAST._IPath _1530_p;
      RAST._IPath _out86;
      _out86 = DCOMP.COMP.GenPath(p, escape);
      _1530_p = _out86;
      e = (_1530_p).AsExpr();
      return e;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi24 = new BigInteger((args).Count);
      for (BigInteger _1531_i = BigInteger.Zero; _1531_i < _hi24; _1531_i++) {
        RAST._IType _1532_genTp;
        RAST._IType _out87;
        _out87 = (this).GenType((args).Select(_1531_i), genTypeContext);
        _1532_genTp = _out87;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1532_genTp));
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
          DAST._IResolvedType _1533_resolved = _source74.dtor_resolved;
          unmatched74 = false;
          {
            RAST._IType _1534_t;
            RAST._IType _out88;
            _out88 = DCOMP.COMP.GenPathType((_1533_resolved).dtor_path);
            _1534_t = _out88;
            Dafny.ISequence<RAST._IType> _1535_typeArgs;
            Dafny.ISequence<RAST._IType> _out89;
            _out89 = (this).GenTypeArgs((_1533_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let20_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let20_0, _1536_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let21_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let21_0, _1537_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1536_dt__update__tmp_h0).dtor_inBinding, (_1536_dt__update__tmp_h0).dtor_inFn, _1537_dt__update_hforTraitParents_h0))))));
            _1535_typeArgs = _out89;
            s = RAST.Type.create_TypeApp(_1534_t, _1535_typeArgs);
            DAST._IResolvedTypeBase _source75 = (_1533_resolved).dtor_kind;
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
                  if ((this).IsRcWrapped((_1533_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched75) {
              if (_source75.is_Trait) {
                unmatched75 = false;
                {
                  if (((_1533_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = RAST.__default.AnyTrait;
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched75) {
              DAST._IType _1538_base = _source75.dtor_baseType;
              DAST._INewtypeRange _1539_range = _source75.dtor_range;
              bool _1540_erased = _source75.dtor_erase;
              unmatched75 = false;
              {
                if (_1540_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source76 = DCOMP.COMP.NewtypeRangeToRustType(_1539_range);
                  bool unmatched76 = true;
                  if (unmatched76) {
                    if (_source76.is_Some) {
                      RAST._IType _1541_v = _source76.dtor_value;
                      unmatched76 = false;
                      s = _1541_v;
                    }
                  }
                  if (unmatched76) {
                    unmatched76 = false;
                    RAST._IType _1542_underlying;
                    RAST._IType _out90;
                    _out90 = (this).GenType(_1538_base, DCOMP.GenTypeContext.@default());
                    _1542_underlying = _out90;
                    s = RAST.Type.create_TSynonym(s, _1542_underlying);
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
          Dafny.ISequence<DAST._IType> _1543_types = _source74.dtor_Tuple_a0;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IType> _1544_args;
            _1544_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1545_i;
            _1545_i = BigInteger.Zero;
            while ((_1545_i) < (new BigInteger((_1543_types).Count))) {
              RAST._IType _1546_generated;
              RAST._IType _out91;
              _out91 = (this).GenType((_1543_types).Select(_1545_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let22_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let22_0, _1547_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let23_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let23_0, _1548_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1547_dt__update__tmp_h1).dtor_inBinding, (_1547_dt__update__tmp_h1).dtor_inFn, _1548_dt__update_hforTraitParents_h1))))));
              _1546_generated = _out91;
              _1544_args = Dafny.Sequence<RAST._IType>.Concat(_1544_args, Dafny.Sequence<RAST._IType>.FromElements(_1546_generated));
              _1545_i = (_1545_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1543_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1544_args)) : (RAST.__default.SystemTupleType(_1544_args)));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Array) {
          DAST._IType _1549_element = _source74.dtor_element;
          BigInteger _1550_dims = _source74.dtor_dims;
          unmatched74 = false;
          {
            if ((_1550_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1551_elem;
              RAST._IType _out92;
              _out92 = (this).GenType(_1549_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let24_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let24_0, _1552_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let25_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let25_0, _1553_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1552_dt__update__tmp_h2).dtor_inBinding, (_1552_dt__update__tmp_h2).dtor_inFn, _1553_dt__update_hforTraitParents_h2))))));
              _1551_elem = _out92;
              if ((_1550_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1551_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1554_n;
                _1554_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1550_dims));
                s = (((RAST.__default.dafny__runtime).MSel(_1554_n)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1551_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Seq) {
          DAST._IType _1555_element = _source74.dtor_element;
          unmatched74 = false;
          {
            RAST._IType _1556_elem;
            RAST._IType _out93;
            _out93 = (this).GenType(_1555_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let26_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let26_0, _1557_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let27_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let27_0, _1558_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1557_dt__update__tmp_h3).dtor_inBinding, (_1557_dt__update__tmp_h3).dtor_inFn, _1558_dt__update_hforTraitParents_h3))))));
            _1556_elem = _out93;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1556_elem));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Set) {
          DAST._IType _1559_element = _source74.dtor_element;
          unmatched74 = false;
          {
            RAST._IType _1560_elem;
            RAST._IType _out94;
            _out94 = (this).GenType(_1559_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let28_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let28_0, _1561_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let29_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let29_0, _1562_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1561_dt__update__tmp_h4).dtor_inBinding, (_1561_dt__update__tmp_h4).dtor_inFn, _1562_dt__update_hforTraitParents_h4))))));
            _1560_elem = _out94;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1560_elem));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Multiset) {
          DAST._IType _1563_element = _source74.dtor_element;
          unmatched74 = false;
          {
            RAST._IType _1564_elem;
            RAST._IType _out95;
            _out95 = (this).GenType(_1563_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let30_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let30_0, _1565_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let31_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let31_0, _1566_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1565_dt__update__tmp_h5).dtor_inBinding, (_1565_dt__update__tmp_h5).dtor_inFn, _1566_dt__update_hforTraitParents_h5))))));
            _1564_elem = _out95;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1564_elem));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Map) {
          DAST._IType _1567_key = _source74.dtor_key;
          DAST._IType _1568_value = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IType _1569_keyType;
            RAST._IType _out96;
            _out96 = (this).GenType(_1567_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let32_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let32_0, _1570_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let33_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let33_0, _1571_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1570_dt__update__tmp_h6).dtor_inBinding, (_1570_dt__update__tmp_h6).dtor_inFn, _1571_dt__update_hforTraitParents_h6))))));
            _1569_keyType = _out96;
            RAST._IType _1572_valueType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1568_value, genTypeContext);
            _1572_valueType = _out97;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1569_keyType, _1572_valueType));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_MapBuilder) {
          DAST._IType _1573_key = _source74.dtor_key;
          DAST._IType _1574_value = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IType _1575_keyType;
            RAST._IType _out98;
            _out98 = (this).GenType(_1573_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let34_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let34_0, _1576_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let35_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let35_0, _1577_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1576_dt__update__tmp_h7).dtor_inBinding, (_1576_dt__update__tmp_h7).dtor_inFn, _1577_dt__update_hforTraitParents_h7))))));
            _1575_keyType = _out98;
            RAST._IType _1578_valueType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1574_value, genTypeContext);
            _1578_valueType = _out99;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1575_keyType, _1578_valueType));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_SetBuilder) {
          DAST._IType _1579_elem = _source74.dtor_element;
          unmatched74 = false;
          {
            RAST._IType _1580_elemType;
            RAST._IType _out100;
            _out100 = (this).GenType(_1579_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let36_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let36_0, _1581_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let37_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let37_0, _1582_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1581_dt__update__tmp_h8).dtor_inBinding, (_1581_dt__update__tmp_h8).dtor_inFn, _1582_dt__update_hforTraitParents_h8))))));
            _1580_elemType = _out100;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1580_elemType));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1583_args = _source74.dtor_args;
          DAST._IType _1584_result = _source74.dtor_result;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IType> _1585_argTypes;
            _1585_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1586_i;
            _1586_i = BigInteger.Zero;
            while ((_1586_i) < (new BigInteger((_1583_args).Count))) {
              RAST._IType _1587_generated;
              RAST._IType _out101;
              _out101 = (this).GenType((_1583_args).Select(_1586_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let38_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let38_0, _1588_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let39_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let39_0, _1589_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let40_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let40_0, _1590_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1588_dt__update__tmp_h9).dtor_inBinding, _1590_dt__update_hinFn_h0, _1589_dt__update_hforTraitParents_h9))))))));
              _1587_generated = _out101;
              _1585_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1585_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1587_generated)));
              _1586_i = (_1586_i) + (BigInteger.One);
            }
            RAST._IType _1591_resultType;
            RAST._IType _out102;
            _out102 = (this).GenType(_1584_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1591_resultType = _out102;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1585_argTypes, _1591_resultType)));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source74.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1592_name = _h90;
          unmatched74 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1592_name));
        }
      }
      if (unmatched74) {
        if (_source74.is_Primitive) {
          DAST._IPrimitive _1593_p = _source74.dtor_Primitive_a0;
          unmatched74 = false;
          {
            DAST._IPrimitive _source77 = _1593_p;
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
        Dafny.ISequence<Dafny.Rune> _1594_v = _source74.dtor_Passthrough_a0;
        unmatched74 = false;
        s = RAST.__default.RawType(_1594_v);
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
      BigInteger _hi25 = new BigInteger((body).Count);
      for (BigInteger _1595_i = BigInteger.Zero; _1595_i < _hi25; _1595_i++) {
        DAST._IMethod _source78 = (body).Select(_1595_i);
        bool unmatched78 = true;
        if (unmatched78) {
          DAST._IMethod _1596_m = _source78;
          unmatched78 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source79 = (_1596_m).dtor_overridingPath;
            bool unmatched79 = true;
            if (unmatched79) {
              if (_source79.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1597_p = _source79.dtor_value;
                unmatched79 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1598_existing;
                  _1598_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1597_p)) {
                    _1598_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1597_p);
                  }
                  if (((new BigInteger(((_1596_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1599_genMethod;
                  RAST._IImplMember _out103;
                  _out103 = (this).GenMethod(_1596_m, true, enclosingType, enclosingTypeParams);
                  _1599_genMethod = _out103;
                  _1598_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1598_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1599_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1597_p, _1598_existing)));
                }
              }
            }
            if (unmatched79) {
              unmatched79 = false;
              {
                RAST._IImplMember _1600_generated;
                RAST._IImplMember _out104;
                _out104 = (this).GenMethod(_1596_m, forTrait, enclosingType, enclosingTypeParams);
                _1600_generated = _out104;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1600_generated));
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
      BigInteger _hi26 = new BigInteger((@params).Count);
      for (BigInteger _1601_i = BigInteger.Zero; _1601_i < _hi26; _1601_i++) {
        DAST._IFormal _1602_param;
        _1602_param = (@params).Select(_1601_i);
        RAST._IType _1603_paramType;
        RAST._IType _out105;
        _out105 = (this).GenType((_1602_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1603_paramType = _out105;
        if (((!((_1603_paramType).CanReadWithoutClone())) || (forLambda)) && (!((_1602_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1603_paramType = RAST.Type.create_Borrowed(_1603_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeVar((_1602_param).dtor_name), _1603_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1604_params;
      Dafny.ISequence<RAST._IFormal> _out106;
      _out106 = (this).GenParams((m).dtor_params, false);
      _1604_params = _out106;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1605_paramNames;
      _1605_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1606_paramTypes;
      _1606_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi27 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1607_paramI = BigInteger.Zero; _1607_paramI < _hi27; _1607_paramI++) {
        DAST._IFormal _1608_dafny__formal;
        _1608_dafny__formal = ((m).dtor_params).Select(_1607_paramI);
        RAST._IFormal _1609_formal;
        _1609_formal = (_1604_params).Select(_1607_paramI);
        Dafny.ISequence<Dafny.Rune> _1610_name;
        _1610_name = (_1609_formal).dtor_name;
        _1605_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1605_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1610_name));
        _1606_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1606_paramTypes, _1610_name, (_1609_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1611_fnName;
      _1611_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1612_selfIdent;
      _1612_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1613_selfId;
        _1613_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1613_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv197 = enclosingTypeParams;
        var _pat_let_tv198 = enclosingType;
        DAST._IType _1614_instanceType;
        _1614_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source80 = enclosingType;
          bool unmatched80 = true;
          if (unmatched80) {
            if (_source80.is_UserDefined) {
              DAST._IResolvedType _1615_r = _source80.dtor_resolved;
              unmatched80 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1615_r, _pat_let41_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let41_0, _1616_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv197, _pat_let42_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let42_0, _1617_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1616_dt__update__tmp_h0).dtor_path, _1617_dt__update_htypeArgs_h0, (_1616_dt__update__tmp_h0).dtor_kind, (_1616_dt__update__tmp_h0).dtor_attributes, (_1616_dt__update__tmp_h0).dtor_properMethods, (_1616_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched80) {
            unmatched80 = false;
            return _pat_let_tv198;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1618_selfFormal;
          _1618_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1604_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1618_selfFormal), _1604_params);
        } else {
          RAST._IType _1619_tpe;
          RAST._IType _out107;
          _out107 = (this).GenType(_1614_instanceType, DCOMP.GenTypeContext.@default());
          _1619_tpe = _out107;
          if ((_1613_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1619_tpe = RAST.Type.create_Borrowed(_1619_tpe);
          } else if ((_1613_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1619_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1619_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1619_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _1619_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.__default.SelfOwned));
              } else {
                _1619_tpe = RAST.Type.create_Borrowed(RAST.__default.SelfOwned);
              }
            }
          }
          _1604_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1613_selfId, _1619_tpe)), _1604_params);
        }
        _1612_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1613_selfId, _1614_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1620_retTypeArgs;
      _1620_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1621_typeI;
      _1621_typeI = BigInteger.Zero;
      while ((_1621_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1622_typeExpr;
        RAST._IType _out108;
        _out108 = (this).GenType(((m).dtor_outTypes).Select(_1621_typeI), DCOMP.GenTypeContext.@default());
        _1622_typeExpr = _out108;
        _1620_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1620_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1622_typeExpr));
        _1621_typeI = (_1621_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1623_visibility;
      _1623_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1624_typeParamsFiltered;
      _1624_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1625_typeParamI = BigInteger.Zero; _1625_typeParamI < _hi28; _1625_typeParamI++) {
        DAST._ITypeArgDecl _1626_typeParam;
        _1626_typeParam = ((m).dtor_typeParams).Select(_1625_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1626_typeParam).dtor_name)))) {
          _1624_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1624_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1626_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1627_typeParams;
      _1627_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1624_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi29 = new BigInteger((_1624_typeParamsFiltered).Count);
        for (BigInteger _1628_i = BigInteger.Zero; _1628_i < _hi29; _1628_i++) {
          DAST._IType _1629_typeArg;
          RAST._ITypeParamDecl _1630_rTypeParamDecl;
          DAST._IType _out109;
          RAST._ITypeParamDecl _out110;
          (this).GenTypeParam((_1624_typeParamsFiltered).Select(_1628_i), out _out109, out _out110);
          _1629_typeArg = _out109;
          _1630_rTypeParamDecl = _out110;
          var _pat_let_tv199 = _1630_rTypeParamDecl;
          _1630_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1630_rTypeParamDecl, _pat_let43_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let43_0, _1631_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv199).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait)), _pat_let44_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let44_0, _1632_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1631_dt__update__tmp_h1).dtor_content, _1632_dt__update_hconstraints_h0)))));
          _1627_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1627_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1630_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1633_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1634_env = DCOMP.Environment.Default();
      RAST._IExpr _1635_preBody;
      _1635_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1636_preAssignNames;
      _1636_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1637_preAssignTypes;
      _1637_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1638_earlyReturn;
        _1638_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source81 = (m).dtor_outVars;
        bool unmatched81 = true;
        if (unmatched81) {
          if (_source81.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1639_outVars = _source81.dtor_value;
            unmatched81 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1638_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi30 = new BigInteger((_1639_outVars).Count);
                for (BigInteger _1640_outI = BigInteger.Zero; _1640_outI < _hi30; _1640_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1641_outVar;
                  _1641_outVar = (_1639_outVars).Select(_1640_outI);
                  Dafny.ISequence<Dafny.Rune> _1642_outName;
                  _1642_outName = DCOMP.__default.escapeVar(_1641_outVar);
                  Dafny.ISequence<Dafny.Rune> _1643_tracker__name;
                  _1643_tracker__name = DCOMP.__default.AddAssignedPrefix(_1642_outName);
                  _1636_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1636_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1643_tracker__name));
                  _1637_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1637_preAssignTypes, _1643_tracker__name, RAST.Type.create_Bool());
                  _1635_preBody = (_1635_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1643_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1644_tupleArgs;
                _1644_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi31 = new BigInteger((_1639_outVars).Count);
                for (BigInteger _1645_outI = BigInteger.Zero; _1645_outI < _hi31; _1645_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1646_outVar;
                  _1646_outVar = (_1639_outVars).Select(_1645_outI);
                  RAST._IType _1647_outType;
                  RAST._IType _out111;
                  _out111 = (this).GenType(((m).dtor_outTypes).Select(_1645_outI), DCOMP.GenTypeContext.@default());
                  _1647_outType = _out111;
                  Dafny.ISequence<Dafny.Rune> _1648_outName;
                  _1648_outName = DCOMP.__default.escapeVar(_1646_outVar);
                  _1605_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1605_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1648_outName));
                  RAST._IType _1649_outMaybeType;
                  _1649_outMaybeType = (((_1647_outType).CanReadWithoutClone()) ? (_1647_outType) : (RAST.__default.MaybePlaceboType(_1647_outType)));
                  _1606_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1606_paramTypes, _1648_outName, _1649_outMaybeType);
                  _1644_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1644_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1648_outName));
                }
                _1638_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_1644_tupleArgs);
              }
            }
          }
        }
        if (unmatched81) {
          unmatched81 = false;
        }
        _1634_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1636_preAssignNames, _1605_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1637_preAssignTypes, _1606_paramTypes));
        RAST._IExpr _1650_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1651___v70;
        DCOMP._IEnvironment _1652___v71;
        RAST._IExpr _out112;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out113;
        DCOMP._IEnvironment _out114;
        (this).GenStmts((m).dtor_body, _1612_selfIdent, _1634_env, true, _1638_earlyReturn, out _out112, out _out113, out _out114);
        _1650_body = _out112;
        _1651___v70 = _out113;
        _1652___v71 = _out114;
        _1633_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1635_preBody).Then(_1650_body));
      } else {
        _1634_env = DCOMP.Environment.create(_1605_paramNames, _1606_paramTypes);
        _1633_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1623_visibility, RAST.Fn.create(_1611_fnName, _1627_typeParams, _1604_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1620_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1620_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1620_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1633_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1653_declarations;
      _1653_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1654_i;
      _1654_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1655_stmts;
      _1655_stmts = stmts;
      while ((_1654_i) < (new BigInteger((_1655_stmts).Count))) {
        DAST._IStatement _1656_stmt;
        _1656_stmt = (_1655_stmts).Select(_1654_i);
        DAST._IStatement _source82 = _1656_stmt;
        bool unmatched82 = true;
        if (unmatched82) {
          if (_source82.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1657_name = _source82.dtor_name;
            DAST._IType _1658_optType = _source82.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source82.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched82 = false;
              if (((_1654_i) + (BigInteger.One)) < (new BigInteger((_1655_stmts).Count))) {
                DAST._IStatement _source83 = (_1655_stmts).Select((_1654_i) + (BigInteger.One));
                bool unmatched83 = true;
                if (unmatched83) {
                  if (_source83.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source83.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> _1659_name2 = lhs0.dtor_ident;
                      DAST._IExpression _1660_rhs = _source83.dtor_value;
                      unmatched83 = false;
                      if (object.Equals(_1659_name2, _1657_name)) {
                        _1655_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1655_stmts).Subsequence(BigInteger.Zero, _1654_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1657_name, _1658_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1660_rhs)))), (_1655_stmts).Drop((_1654_i) + (new BigInteger(2))));
                        _1656_stmt = (_1655_stmts).Select(_1654_i);
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
        RAST._IExpr _1661_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1662_recIdents;
        DCOMP._IEnvironment _1663_newEnv2;
        RAST._IExpr _out115;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
        DCOMP._IEnvironment _out117;
        (this).GenStmt(_1656_stmt, selfIdent, newEnv, (isLast) && ((_1654_i) == ((new BigInteger((_1655_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out115, out _out116, out _out117);
        _1661_stmtExpr = _out115;
        _1662_recIdents = _out116;
        _1663_newEnv2 = _out117;
        newEnv = _1663_newEnv2;
        DAST._IStatement _source84 = _1656_stmt;
        bool unmatched84 = true;
        if (unmatched84) {
          if (_source84.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1664_name = _source84.dtor_name;
            unmatched84 = false;
            {
              _1653_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1653_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_1664_name)));
            }
          }
        }
        if (unmatched84) {
          unmatched84 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1662_recIdents, _1653_declarations));
        generated = (generated).Then(_1661_stmtExpr);
        _1654_i = (_1654_i) + (BigInteger.One);
        if ((_1661_stmtExpr).is_Return) {
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
          Dafny.ISequence<Dafny.Rune> _1665_id = _source85.dtor_ident;
          unmatched85 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1666_idRust;
            _1666_idRust = DCOMP.__default.escapeVar(_1665_id);
            if (((env).IsBorrowed(_1666_idRust)) || ((env).IsBorrowedMut(_1666_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1666_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1666_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1666_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched85) {
        if (_source85.is_Select) {
          DAST._IExpression _1667_on = _source85.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1668_field = _source85.dtor_field;
          unmatched85 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1669_fieldName;
            _1669_fieldName = DCOMP.__default.escapeVar(_1668_field);
            RAST._IExpr _1670_onExpr;
            DCOMP._IOwnership _1671_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1672_recIdents;
            RAST._IExpr _out118;
            DCOMP._IOwnership _out119;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
            (this).GenExpr(_1667_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out118, out _out119, out _out120);
            _1670_onExpr = _out118;
            _1671_onOwned = _out119;
            _1672_recIdents = _out120;
            RAST._IExpr _source86 = _1670_onExpr;
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
                Dafny.ISequence<Dafny.Rune> _1673_isAssignedVar;
                _1673_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1669_fieldName);
                if (((newEnv).dtor_names).Contains(_1673_isAssignedVar)) {
                  generated = (((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1669_fieldName), RAST.Expr.create_Identifier(_1673_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1673_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1673_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1669_fieldName, rhs);
                }
              }
            }
            if (unmatched86) {
              unmatched86 = false;
              if (!object.Equals(_1670_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1670_onExpr = ((this).modify__macro).Apply1(_1670_onExpr);
              }
              generated = RAST.__default.AssignMember(_1670_onExpr, _1669_fieldName, rhs);
            }
            readIdents = _1672_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched85) {
        DAST._IExpression _1674_on = _source85.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1675_indices = _source85.dtor_indices;
        unmatched85 = false;
        {
          RAST._IExpr _1676_onExpr;
          DCOMP._IOwnership _1677_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1678_recIdents;
          RAST._IExpr _out121;
          DCOMP._IOwnership _out122;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
          (this).GenExpr(_1674_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out121, out _out122, out _out123);
          _1676_onExpr = _out121;
          _1677_onOwned = _out122;
          _1678_recIdents = _out123;
          readIdents = _1678_recIdents;
          _1676_onExpr = ((this).modify__macro).Apply1(_1676_onExpr);
          RAST._IExpr _1679_r;
          _1679_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1680_indicesExpr;
          _1680_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_1675_indices).Count);
          for (BigInteger _1681_i = BigInteger.Zero; _1681_i < _hi32; _1681_i++) {
            RAST._IExpr _1682_idx;
            DCOMP._IOwnership _1683___v80;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1684_recIdentsIdx;
            RAST._IExpr _out124;
            DCOMP._IOwnership _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            (this).GenExpr((_1675_indices).Select(_1681_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out124, out _out125, out _out126);
            _1682_idx = _out124;
            _1683___v80 = _out125;
            _1684_recIdentsIdx = _out126;
            Dafny.ISequence<Dafny.Rune> _1685_varName;
            _1685_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1681_i));
            _1680_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1680_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1685_varName)));
            _1679_r = (_1679_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1685_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1682_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1684_recIdentsIdx);
          }
          if ((new BigInteger((_1675_indices).Count)) > (BigInteger.One)) {
            _1676_onExpr = (_1676_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1686_rhs;
          _1686_rhs = rhs;
          var _pat_let_tv200 = env;
          if (((_1676_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1676_onExpr).LhsIdentifierName(), _pat_let45_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let45_0, _1687_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv200).GetType(_1687_name), _pat_let46_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let46_0, _1688_tpe => ((_1688_tpe).is_Some) && (((_1688_tpe).dtor_value).IsUninitArray())))))))) {
            _1686_rhs = RAST.__default.MaybeUninitNew(_1686_rhs);
          }
          generated = (_1679_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1676_onExpr, _1680_indicesExpr)), _1686_rhs));
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
          Dafny.ISequence<DAST._IFormal> _1689_fields = _source87.dtor_fields;
          unmatched87 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi33 = new BigInteger((_1689_fields).Count);
            for (BigInteger _1690_i = BigInteger.Zero; _1690_i < _hi33; _1690_i++) {
              DAST._IFormal _1691_field;
              _1691_field = (_1689_fields).Select(_1690_i);
              Dafny.ISequence<Dafny.Rune> _1692_fieldName;
              _1692_fieldName = DCOMP.__default.escapeVar((_1691_field).dtor_name);
              RAST._IType _1693_fieldTyp;
              RAST._IType _out127;
              _out127 = (this).GenType((_1691_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1693_fieldTyp = _out127;
              Dafny.ISequence<Dafny.Rune> _1694_isAssignedVar;
              _1694_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1692_fieldName);
              if (((newEnv).dtor_names).Contains(_1694_isAssignedVar)) {
                RAST._IExpr _1695_rhs;
                DCOMP._IOwnership _1696___v81;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1697___v82;
                RAST._IExpr _out128;
                DCOMP._IOwnership _out129;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1691_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out128, out _out129, out _out130);
                _1695_rhs = _out128;
                _1696___v81 = _out129;
                _1697___v82 = _out130;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1694_isAssignedVar));
                generated = (generated).Then((((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1692_fieldName), RAST.Expr.create_Identifier(_1694_isAssignedVar), _1695_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1694_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1698_name = _source87.dtor_name;
          DAST._IType _1699_typ = _source87.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source87.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1700_expression = maybeValue1.dtor_value;
            unmatched87 = false;
            {
              RAST._IType _1701_tpe;
              RAST._IType _out131;
              _out131 = (this).GenType(_1699_typ, DCOMP.GenTypeContext.InBinding());
              _1701_tpe = _out131;
              Dafny.ISequence<Dafny.Rune> _1702_varName;
              _1702_varName = DCOMP.__default.escapeVar(_1698_name);
              bool _1703_hasCopySemantics;
              _1703_hasCopySemantics = (_1701_tpe).CanReadWithoutClone();
              if (((_1700_expression).is_InitializationValue) && (!(_1703_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1702_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.MaybePlaceboPath).AsExpr()).ApplyType1(_1701_tpe)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1702_varName, RAST.__default.MaybePlaceboType(_1701_tpe));
              } else {
                RAST._IExpr _1704_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1705_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1700_expression).is_InitializationValue) && ((_1701_tpe).IsObjectOrPointer())) {
                  _1704_expr = (_1701_tpe).ToNullExpr();
                  _1705_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1706_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out132;
                  DCOMP._IOwnership _out133;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out134;
                  (this).GenExpr(_1700_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out132, out _out133, out _out134);
                  _1704_expr = _out132;
                  _1706_exprOwnership = _out133;
                  _1705_recIdents = _out134;
                }
                readIdents = _1705_recIdents;
                _1701_tpe = (((_1700_expression).is_NewUninitArray) ? ((_1701_tpe).TypeAtInitialization()) : (_1701_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1702_varName, Std.Wrappers.Option<RAST._IType>.create_Some(_1701_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1704_expr));
                newEnv = (env).AddAssigned(_1702_varName, _1701_tpe);
              }
            }
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1707_name = _source87.dtor_name;
          DAST._IType _1708_typ = _source87.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source87.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched87 = false;
            {
              DAST._IStatement _1709_newStmt;
              _1709_newStmt = DAST.Statement.create_DeclareVar(_1707_name, _1708_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1708_typ)));
              RAST._IExpr _out135;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out136;
              DCOMP._IEnvironment _out137;
              (this).GenStmt(_1709_newStmt, selfIdent, env, isLast, earlyReturn, out _out135, out _out136, out _out137);
              generated = _out135;
              readIdents = _out136;
              newEnv = _out137;
            }
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Assign) {
          DAST._IAssignLhs _1710_lhs = _source87.dtor_lhs;
          DAST._IExpression _1711_expression = _source87.dtor_value;
          unmatched87 = false;
          {
            RAST._IExpr _1712_exprGen;
            DCOMP._IOwnership _1713___v83;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1714_exprIdents;
            RAST._IExpr _out138;
            DCOMP._IOwnership _out139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
            (this).GenExpr(_1711_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out138, out _out139, out _out140);
            _1712_exprGen = _out138;
            _1713___v83 = _out139;
            _1714_exprIdents = _out140;
            if ((_1710_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1715_rustId;
              _1715_rustId = DCOMP.__default.escapeVar((_1710_lhs).dtor_ident);
              Std.Wrappers._IOption<RAST._IType> _1716_tpe;
              _1716_tpe = (env).GetType(_1715_rustId);
              if (((_1716_tpe).is_Some) && ((((_1716_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1712_exprGen = RAST.__default.MaybePlacebo(_1712_exprGen);
              }
            }
            if (((_1710_lhs).is_Index) && (((_1710_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1717_rustId;
              _1717_rustId = DCOMP.__default.escapeVar(((_1710_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1718_tpe;
              _1718_tpe = (env).GetType(_1717_rustId);
              if (((_1718_tpe).is_Some) && ((((_1718_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1712_exprGen = RAST.__default.MaybeUninitNew(_1712_exprGen);
              }
            }
            RAST._IExpr _1719_lhsGen;
            bool _1720_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1721_recIdents;
            DCOMP._IEnvironment _1722_resEnv;
            RAST._IExpr _out141;
            bool _out142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
            DCOMP._IEnvironment _out144;
            (this).GenAssignLhs(_1710_lhs, _1712_exprGen, selfIdent, env, out _out141, out _out142, out _out143, out _out144);
            _1719_lhsGen = _out141;
            _1720_needsIIFE = _out142;
            _1721_recIdents = _out143;
            _1722_resEnv = _out144;
            generated = _1719_lhsGen;
            newEnv = _1722_resEnv;
            if (_1720_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1721_recIdents, _1714_exprIdents);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_If) {
          DAST._IExpression _1723_cond = _source87.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1724_thnDafny = _source87.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1725_elsDafny = _source87.dtor_els;
          unmatched87 = false;
          {
            RAST._IExpr _1726_cond;
            DCOMP._IOwnership _1727___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1728_recIdents;
            RAST._IExpr _out145;
            DCOMP._IOwnership _out146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
            (this).GenExpr(_1723_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out145, out _out146, out _out147);
            _1726_cond = _out145;
            _1727___v84 = _out146;
            _1728_recIdents = _out147;
            Dafny.ISequence<Dafny.Rune> _1729_condString;
            _1729_condString = (_1726_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1728_recIdents;
            RAST._IExpr _1730_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1731_thnIdents;
            DCOMP._IEnvironment _1732_thnEnv;
            RAST._IExpr _out148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
            DCOMP._IEnvironment _out150;
            (this).GenStmts(_1724_thnDafny, selfIdent, env, isLast, earlyReturn, out _out148, out _out149, out _out150);
            _1730_thn = _out148;
            _1731_thnIdents = _out149;
            _1732_thnEnv = _out150;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1731_thnIdents);
            RAST._IExpr _1733_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1734_elsIdents;
            DCOMP._IEnvironment _1735_elsEnv;
            RAST._IExpr _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP._IEnvironment _out153;
            (this).GenStmts(_1725_elsDafny, selfIdent, env, isLast, earlyReturn, out _out151, out _out152, out _out153);
            _1733_els = _out151;
            _1734_elsIdents = _out152;
            _1735_elsEnv = _out153;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1734_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1726_cond, _1730_thn, _1733_els);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1736_lbl = _source87.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1737_body = _source87.dtor_body;
          unmatched87 = false;
          {
            RAST._IExpr _1738_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1739_bodyIdents;
            DCOMP._IEnvironment _1740_env2;
            RAST._IExpr _out154;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out155;
            DCOMP._IEnvironment _out156;
            (this).GenStmts(_1737_body, selfIdent, env, isLast, earlyReturn, out _out154, out _out155, out _out156);
            _1738_body = _out154;
            _1739_bodyIdents = _out155;
            _1740_env2 = _out156;
            readIdents = _1739_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1736_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1738_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_While) {
          DAST._IExpression _1741_cond = _source87.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1742_body = _source87.dtor_body;
          unmatched87 = false;
          {
            RAST._IExpr _1743_cond;
            DCOMP._IOwnership _1744___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1745_recIdents;
            RAST._IExpr _out157;
            DCOMP._IOwnership _out158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
            (this).GenExpr(_1741_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out157, out _out158, out _out159);
            _1743_cond = _out157;
            _1744___v85 = _out158;
            _1745_recIdents = _out159;
            readIdents = _1745_recIdents;
            RAST._IExpr _1746_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1747_bodyIdents;
            DCOMP._IEnvironment _1748_bodyEnv;
            RAST._IExpr _out160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out161;
            DCOMP._IEnvironment _out162;
            (this).GenStmts(_1742_body, selfIdent, env, false, earlyReturn, out _out160, out _out161, out _out162);
            _1746_bodyExpr = _out160;
            _1747_bodyIdents = _out161;
            _1748_bodyEnv = _out162;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1747_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1743_cond), _1746_bodyExpr);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1749_boundName = _source87.dtor_boundName;
          DAST._IType _1750_boundType = _source87.dtor_boundType;
          DAST._IExpression _1751_overExpr = _source87.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1752_body = _source87.dtor_body;
          unmatched87 = false;
          {
            RAST._IExpr _1753_over;
            DCOMP._IOwnership _1754___v86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1755_recIdents;
            RAST._IExpr _out163;
            DCOMP._IOwnership _out164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
            (this).GenExpr(_1751_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out163, out _out164, out _out165);
            _1753_over = _out163;
            _1754___v86 = _out164;
            _1755_recIdents = _out165;
            if (((_1751_overExpr).is_MapBoundedPool) || ((_1751_overExpr).is_SetBoundedPool)) {
              _1753_over = ((_1753_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1756_boundTpe;
            RAST._IType _out166;
            _out166 = (this).GenType(_1750_boundType, DCOMP.GenTypeContext.@default());
            _1756_boundTpe = _out166;
            readIdents = _1755_recIdents;
            Dafny.ISequence<Dafny.Rune> _1757_boundRName;
            _1757_boundRName = DCOMP.__default.escapeVar(_1749_boundName);
            RAST._IExpr _1758_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1759_bodyIdents;
            DCOMP._IEnvironment _1760_bodyEnv;
            RAST._IExpr _out167;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out168;
            DCOMP._IEnvironment _out169;
            (this).GenStmts(_1752_body, selfIdent, (env).AddAssigned(_1757_boundRName, _1756_boundTpe), false, earlyReturn, out _out167, out _out168, out _out169);
            _1758_bodyExpr = _out167;
            _1759_bodyIdents = _out168;
            _1760_bodyEnv = _out169;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1759_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1757_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1757_boundRName, _1753_over, _1758_bodyExpr);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1761_toLabel = _source87.dtor_toLabel;
          unmatched87 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source88 = _1761_toLabel;
            bool unmatched88 = true;
            if (unmatched88) {
              if (_source88.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1762_lbl = _source88.dtor_value;
                unmatched88 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1762_lbl)));
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
          Dafny.ISequence<DAST._IStatement> _1763_body = _source87.dtor_body;
          unmatched87 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1764_selfClone;
              DCOMP._IOwnership _1765___v87;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1766___v88;
              RAST._IExpr _out170;
              DCOMP._IOwnership _out171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out172;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out170, out _out171, out _out172);
              _1764_selfClone = _out170;
              _1765___v87 = _out171;
              _1766___v88 = _out172;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1764_selfClone)));
            }
            newEnv = env;
            BigInteger _hi34 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1767_paramI = BigInteger.Zero; _1767_paramI < _hi34; _1767_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1768_param;
              _1768_param = ((env).dtor_names).Select(_1767_paramI);
              RAST._IExpr _1769_paramInit;
              DCOMP._IOwnership _1770___v89;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1771___v90;
              RAST._IExpr _out173;
              DCOMP._IOwnership _out174;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out175;
              (this).GenIdent(_1768_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out173, out _out174, out _out175);
              _1769_paramInit = _out173;
              _1770___v89 = _out174;
              _1771___v90 = _out175;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1768_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1769_paramInit)));
              if (((env).dtor_types).Contains(_1768_param)) {
                RAST._IType _1772_declaredType;
                _1772_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1768_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1768_param, _1772_declaredType);
              }
            }
            RAST._IExpr _1773_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1774_bodyIdents;
            DCOMP._IEnvironment _1775_bodyEnv;
            RAST._IExpr _out176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
            DCOMP._IEnvironment _out178;
            (this).GenStmts(_1763_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out176, out _out177, out _out178);
            _1773_bodyExpr = _out176;
            _1774_bodyIdents = _out177;
            _1775_bodyEnv = _out178;
            readIdents = _1774_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1773_bodyExpr)));
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
          DAST._IExpression _1776_on = _source87.dtor_on;
          DAST._ICallName _1777_name = _source87.dtor_callName;
          Dafny.ISequence<DAST._IType> _1778_typeArgs = _source87.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1779_args = _source87.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1780_maybeOutVars = _source87.dtor_outs;
          unmatched87 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1781_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1782_recIdents;
            Dafny.ISequence<RAST._IType> _1783_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1784_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out180;
            Dafny.ISequence<RAST._IType> _out181;
            Std.Wrappers._IOption<DAST._IResolvedType> _out182;
            (this).GenArgs(selfIdent, _1777_name, _1778_typeArgs, _1779_args, env, out _out179, out _out180, out _out181, out _out182);
            _1781_argExprs = _out179;
            _1782_recIdents = _out180;
            _1783_typeExprs = _out181;
            _1784_fullNameQualifier = _out182;
            readIdents = _1782_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source89 = _1784_fullNameQualifier;
            bool unmatched89 = true;
            if (unmatched89) {
              if (_source89.is_Some) {
                DAST._IResolvedType value9 = _source89.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1785_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1786_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1787_base = value9.dtor_kind;
                unmatched89 = false;
                RAST._IExpr _1788_fullPath;
                RAST._IExpr _out183;
                _out183 = DCOMP.COMP.GenPathExpr(_1785_path, true);
                _1788_fullPath = _out183;
                Dafny.ISequence<RAST._IType> _1789_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out184;
                _out184 = (this).GenTypeArgs(_1786_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1789_onTypeExprs = _out184;
                RAST._IExpr _1790_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1791_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1792_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1787_base).is_Trait) || ((_1787_base).is_Class)) {
                  RAST._IExpr _out185;
                  DCOMP._IOwnership _out186;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out187;
                  (this).GenExpr(_1776_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out185, out _out186, out _out187);
                  _1790_onExpr = _out185;
                  _1791_recOwnership = _out186;
                  _1792_recIdents = _out187;
                  _1790_onExpr = ((this).modify__macro).Apply1(_1790_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1792_recIdents);
                } else {
                  RAST._IExpr _out188;
                  DCOMP._IOwnership _out189;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
                  (this).GenExpr(_1776_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out188, out _out189, out _out190);
                  _1790_onExpr = _out188;
                  _1791_recOwnership = _out189;
                  _1792_recIdents = _out190;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1792_recIdents);
                }
                generated = ((((_1788_fullPath).ApplyType(_1789_onTypeExprs)).FSel(DCOMP.__default.escapeName((_1777_name).dtor_name))).ApplyType(_1783_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1790_onExpr), _1781_argExprs));
              }
            }
            if (unmatched89) {
              unmatched89 = false;
              RAST._IExpr _1793_onExpr;
              DCOMP._IOwnership _1794___v95;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1795_enclosingIdents;
              RAST._IExpr _out191;
              DCOMP._IOwnership _out192;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
              (this).GenExpr(_1776_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out191, out _out192, out _out193);
              _1793_onExpr = _out191;
              _1794___v95 = _out192;
              _1795_enclosingIdents = _out193;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1795_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1796_renderedName;
              _1796_renderedName = (this).GetMethodName(_1776_on, _1777_name);
              DAST._IExpression _source90 = _1776_on;
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
                    _1793_onExpr = (_1793_onExpr).FSel(_1796_renderedName);
                  }
                }
              }
              if (unmatched90) {
                unmatched90 = false;
                {
                  if (!object.Equals(_1793_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source91 = _1777_name;
                    bool unmatched91 = true;
                    if (unmatched91) {
                      if (_source91.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source91.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1797_tpe = onType0.dtor_value;
                          unmatched91 = false;
                          RAST._IType _1798_typ;
                          RAST._IType _out194;
                          _out194 = (this).GenType(_1797_tpe, DCOMP.GenTypeContext.@default());
                          _1798_typ = _out194;
                          if (((_1798_typ).IsObjectOrPointer()) && (!object.Equals(_1793_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1793_onExpr = ((this).modify__macro).Apply1(_1793_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched91) {
                      unmatched91 = false;
                    }
                  }
                  _1793_onExpr = (_1793_onExpr).Sel(_1796_renderedName);
                }
              }
              generated = ((_1793_onExpr).ApplyType(_1783_typeExprs)).Apply(_1781_argExprs);
            }
            if (((_1780_maybeOutVars).is_Some) && ((new BigInteger(((_1780_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1799_outVar;
              _1799_outVar = DCOMP.__default.escapeVar(((_1780_maybeOutVars).dtor_value).Select(BigInteger.Zero));
              if (!((env).CanReadWithoutClone(_1799_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1799_outVar, generated);
            } else if (((_1780_maybeOutVars).is_None) || ((new BigInteger(((_1780_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1800_tmpVar;
              _1800_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1801_tmpId;
              _1801_tmpId = RAST.Expr.create_Identifier(_1800_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1800_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1802_outVars;
              _1802_outVars = (_1780_maybeOutVars).dtor_value;
              BigInteger _hi35 = new BigInteger((_1802_outVars).Count);
              for (BigInteger _1803_outI = BigInteger.Zero; _1803_outI < _hi35; _1803_outI++) {
                Dafny.ISequence<Dafny.Rune> _1804_outVar;
                _1804_outVar = DCOMP.__default.escapeVar((_1802_outVars).Select(_1803_outI));
                RAST._IExpr _1805_rhs;
                _1805_rhs = (_1801_tmpId).Sel(Std.Strings.__default.OfNat(_1803_outI));
                if (!((env).CanReadWithoutClone(_1804_outVar))) {
                  _1805_rhs = RAST.__default.MaybePlacebo(_1805_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1804_outVar, _1805_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Return) {
          DAST._IExpression _1806_exprDafny = _source87.dtor_expr;
          unmatched87 = false;
          {
            RAST._IExpr _1807_expr;
            DCOMP._IOwnership _1808___v105;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1809_recIdents;
            RAST._IExpr _out195;
            DCOMP._IOwnership _out196;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
            (this).GenExpr(_1806_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out195, out _out196, out _out197);
            _1807_expr = _out195;
            _1808___v105 = _out196;
            _1809_recIdents = _out197;
            readIdents = _1809_recIdents;
            if (isLast) {
              generated = _1807_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1807_expr));
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
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1810_rustIdents = _source92.dtor_value;
              unmatched92 = false;
              Dafny.ISequence<RAST._IExpr> _1811_tupleArgs;
              _1811_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi36 = new BigInteger((_1810_rustIdents).Count);
              for (BigInteger _1812_i = BigInteger.Zero; _1812_i < _hi36; _1812_i++) {
                RAST._IExpr _1813_rIdent;
                DCOMP._IOwnership _1814___v106;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1815___v107;
                RAST._IExpr _out198;
                DCOMP._IOwnership _out199;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out200;
                (this).GenIdent((_1810_rustIdents).Select(_1812_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out198, out _out199, out _out200);
                _1813_rIdent = _out198;
                _1814___v106 = _out199;
                _1815___v107 = _out200;
                _1811_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1811_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1813_rIdent));
              }
              if ((new BigInteger((_1811_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1811_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1811_tupleArgs)));
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
        DAST._IExpression _1816_e = _source87.dtor_Print_a0;
        unmatched87 = false;
        {
          RAST._IExpr _1817_printedExpr;
          DCOMP._IOwnership _1818_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1819_recIdents;
          RAST._IExpr _out201;
          DCOMP._IOwnership _out202;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out203;
          (this).GenExpr(_1816_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out201, out _out202, out _out203);
          _1817_printedExpr = _out201;
          _1818_recOwnership = _out202;
          _1819_recIdents = _out203;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).AsExpr()).Apply1(_1817_printedExpr)));
          readIdents = _1819_recIdents;
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
        RAST._IExpr _out204;
        DCOMP._IOwnership _out205;
        (this).FromOwned(r, expectedOwnership, out _out204, out _out205);
        @out = _out204;
        resultingOwnership = _out205;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out206;
        DCOMP._IOwnership _out207;
        (this).FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out206, out _out207);
        @out = _out206;
        resultingOwnership = _out207;
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
            bool _1820_b = _h170.dtor_BoolLiteral_a0;
            unmatched94 = false;
            {
              RAST._IExpr _out208;
              DCOMP._IOwnership _out209;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1820_b), expectedOwnership, out _out208, out _out209);
              r = _out208;
              resultingOwnership = _out209;
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
            Dafny.ISequence<Dafny.Rune> _1821_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1822_t = _h171.dtor_IntLiteral_a1;
            unmatched94 = false;
            {
              DAST._IType _source95 = _1822_t;
              bool unmatched95 = true;
              if (unmatched95) {
                if (_source95.is_Primitive) {
                  DAST._IPrimitive _h70 = _source95.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched95 = false;
                    {
                      if ((new BigInteger((_1821_i).Count)) <= (new BigInteger(4))) {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralInt(_1821_i));
                      } else {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1821_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched95) {
                DAST._IType _1823_o = _source95;
                unmatched95 = false;
                {
                  RAST._IType _1824_genType;
                  RAST._IType _out210;
                  _out210 = (this).GenType(_1823_o, DCOMP.GenTypeContext.@default());
                  _1824_genType = _out210;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1821_i), _1824_genType);
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
      if (unmatched94) {
        if (_source94.is_Literal) {
          DAST._ILiteral _h172 = _source94.dtor_Literal_a0;
          if (_h172.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1825_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1826_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1827_t = _h172.dtor_DecLiteral_a2;
            unmatched94 = false;
            {
              DAST._IType _source96 = _1827_t;
              bool unmatched96 = true;
              if (unmatched96) {
                if (_source96.is_Primitive) {
                  DAST._IPrimitive _h71 = _source96.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched96 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1825_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1826_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched96) {
                DAST._IType _1828_o = _source96;
                unmatched96 = false;
                {
                  RAST._IType _1829_genType;
                  RAST._IType _out213;
                  _out213 = (this).GenType(_1828_o, DCOMP.GenTypeContext.@default());
                  _1829_genType = _out213;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1825_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1826_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1829_genType);
                }
              }
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
      if (unmatched94) {
        if (_source94.is_Literal) {
          DAST._ILiteral _h173 = _source94.dtor_Literal_a0;
          if (_h173.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1830_l = _h173.dtor_StringLiteral_a0;
            bool _1831_verbatim = _h173.dtor_verbatim;
            unmatched94 = false;
            {
              if (_1831_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = (((RAST.__default.dafny__runtime).MSel((this).string__of)).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1830_l, false, _1831_verbatim));
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
      if (unmatched94) {
        if (_source94.is_Literal) {
          DAST._ILiteral _h174 = _source94.dtor_Literal_a0;
          if (_h174.is_CharLiteralUTF16) {
            BigInteger _1832_c = _h174.dtor_CharLiteralUTF16_a0;
            unmatched94 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1832_c));
              r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              r = (((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(r);
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
      if (unmatched94) {
        if (_source94.is_Literal) {
          DAST._ILiteral _h175 = _source94.dtor_Literal_a0;
          if (_h175.is_CharLiteral) {
            Dafny.Rune _1833_c = _h175.dtor_CharLiteral_a0;
            unmatched94 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1833_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(r);
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
      }
      if (unmatched94) {
        DAST._ILiteral _h176 = _source94.dtor_Literal_a0;
        DAST._IType _1834_tpe = _h176.dtor_Null_a0;
        unmatched94 = false;
        {
          RAST._IType _1835_tpeGen;
          RAST._IType _out222;
          _out222 = (this).GenType(_1834_tpe, DCOMP.GenTypeContext.@default());
          _1835_tpeGen = _out222;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null_mut"));
          } else {
            r = RAST.Expr.create_TypeAscription((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1835_tpeGen);
          }
          RAST._IExpr _out223;
          DCOMP._IOwnership _out224;
          (this).FromOwned(r, expectedOwnership, out _out223, out _out224);
          r = _out223;
          resultingOwnership = _out224;
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
      DAST._IBinOp _1836_op = _let_tmp_rhs54.dtor_op;
      DAST._IExpression _1837_lExpr = _let_tmp_rhs54.dtor_left;
      DAST._IExpression _1838_rExpr = _let_tmp_rhs54.dtor_right;
      DAST.Format._IBinaryOpFormat _1839_format = _let_tmp_rhs54.dtor_format2;
      bool _1840_becomesLeftCallsRight;
      _1840_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source97 = _1836_op;
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
      bool _1841_becomesRightCallsLeft;
      _1841_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source98 = _1836_op;
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
      bool _1842_becomesCallLeftRight;
      _1842_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source99 = _1836_op;
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
      DCOMP._IOwnership _1843_expectedLeftOwnership;
      _1843_expectedLeftOwnership = ((_1840_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1841_becomesRightCallsLeft) || (_1842_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1844_expectedRightOwnership;
      _1844_expectedRightOwnership = (((_1840_becomesLeftCallsRight) || (_1842_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1841_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1845_left;
      DCOMP._IOwnership _1846___v112;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1847_recIdentsL;
      RAST._IExpr _out225;
      DCOMP._IOwnership _out226;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
      (this).GenExpr(_1837_lExpr, selfIdent, env, _1843_expectedLeftOwnership, out _out225, out _out226, out _out227);
      _1845_left = _out225;
      _1846___v112 = _out226;
      _1847_recIdentsL = _out227;
      RAST._IExpr _1848_right;
      DCOMP._IOwnership _1849___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1850_recIdentsR;
      RAST._IExpr _out228;
      DCOMP._IOwnership _out229;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out230;
      (this).GenExpr(_1838_rExpr, selfIdent, env, _1844_expectedRightOwnership, out _out228, out _out229, out _out230);
      _1848_right = _out228;
      _1849___v113 = _out229;
      _1850_recIdentsR = _out230;
      DAST._IBinOp _source100 = _1836_op;
      bool unmatched100 = true;
      if (unmatched100) {
        if (_source100.is_In) {
          unmatched100 = false;
          {
            r = ((_1848_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1845_left);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_SeqProperPrefix) {
          unmatched100 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1845_left, _1848_right, _1839_format);
        }
      }
      if (unmatched100) {
        if (_source100.is_SeqPrefix) {
          unmatched100 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1845_left, _1848_right, _1839_format);
        }
      }
      if (unmatched100) {
        if (_source100.is_SetMerge) {
          unmatched100 = false;
          {
            r = ((_1845_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1848_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_SetSubtraction) {
          unmatched100 = false;
          {
            r = ((_1845_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1848_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_SetIntersection) {
          unmatched100 = false;
          {
            r = ((_1845_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1848_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_Subset) {
          unmatched100 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1845_left, _1848_right, _1839_format);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_ProperSubset) {
          unmatched100 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1845_left, _1848_right, _1839_format);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_SetDisjoint) {
          unmatched100 = false;
          {
            r = ((_1845_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1848_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MapMerge) {
          unmatched100 = false;
          {
            r = ((_1845_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1848_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MapSubtraction) {
          unmatched100 = false;
          {
            r = ((_1845_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1848_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MultisetMerge) {
          unmatched100 = false;
          {
            r = ((_1845_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1848_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MultisetSubtraction) {
          unmatched100 = false;
          {
            r = ((_1845_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1848_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MultisetIntersection) {
          unmatched100 = false;
          {
            r = ((_1845_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1848_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_Submultiset) {
          unmatched100 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1845_left, _1848_right, _1839_format);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_ProperSubmultiset) {
          unmatched100 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1845_left, _1848_right, _1839_format);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MultisetDisjoint) {
          unmatched100 = false;
          {
            r = ((_1845_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1848_right);
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_Concat) {
          unmatched100 = false;
          {
            r = ((_1845_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1848_right);
          }
        }
      }
      if (unmatched100) {
        unmatched100 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1836_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1836_op), _1845_left, _1848_right, _1839_format);
          } else {
            DAST._IBinOp _source101 = _1836_op;
            bool unmatched101 = true;
            if (unmatched101) {
              if (_source101.is_Eq) {
                bool _1851_referential = _source101.dtor_referential;
                unmatched101 = false;
                {
                  if (_1851_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1845_left, _1848_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1838_rExpr).is_SeqValue) && ((new BigInteger(((_1838_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1845_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1837_lExpr).is_SeqValue) && ((new BigInteger(((_1837_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1848_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1845_left, _1848_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched101) {
              if (_source101.is_EuclidianDiv) {
                unmatched101 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1845_left, _1848_right));
                }
              }
            }
            if (unmatched101) {
              if (_source101.is_EuclidianMod) {
                unmatched101 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1845_left, _1848_right));
                }
              }
            }
            if (unmatched101) {
              Dafny.ISequence<Dafny.Rune> _1852_op = _source101.dtor_Passthrough_a0;
              unmatched101 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1852_op, _1845_left, _1848_right, _1839_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out231;
      DCOMP._IOwnership _out232;
      (this).FromOwned(r, expectedOwnership, out _out231, out _out232);
      r = _out231;
      resultingOwnership = _out232;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1847_recIdentsL, _1850_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1853_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1854_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1855_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1855_toTpe;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1856_path = _let_tmp_rhs57.dtor_path;
      Dafny.ISequence<DAST._IType> _1857_typeArgs = _let_tmp_rhs57.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs58 = _let_tmp_rhs57.dtor_kind;
      DAST._IType _1858_b = _let_tmp_rhs58.dtor_baseType;
      DAST._INewtypeRange _1859_range = _let_tmp_rhs58.dtor_range;
      bool _1860_erase = _let_tmp_rhs58.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1861___v115 = _let_tmp_rhs57.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1862___v116 = _let_tmp_rhs57.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1863___v117 = _let_tmp_rhs57.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1864_nativeToType;
      _1864_nativeToType = DCOMP.COMP.NewtypeRangeToRustType(_1859_range);
      if (object.Equals(_1854_fromTpe, _1858_b)) {
        RAST._IExpr _1865_recursiveGen;
        DCOMP._IOwnership _1866_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1867_recIdents;
        RAST._IExpr _out233;
        DCOMP._IOwnership _out234;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out235;
        (this).GenExpr(_1853_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out233, out _out234, out _out235);
        _1865_recursiveGen = _out233;
        _1866_recOwned = _out234;
        _1867_recIdents = _out235;
        readIdents = _1867_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source102 = _1864_nativeToType;
        bool unmatched102 = true;
        if (unmatched102) {
          if (_source102.is_Some) {
            RAST._IType _1868_v = _source102.dtor_value;
            unmatched102 = false;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1865_recursiveGen, RAST.Expr.create_ExprFromType(_1868_v)));
            RAST._IExpr _out236;
            DCOMP._IOwnership _out237;
            (this).FromOwned(r, expectedOwnership, out _out236, out _out237);
            r = _out236;
            resultingOwnership = _out237;
          }
        }
        if (unmatched102) {
          unmatched102 = false;
          if (_1860_erase) {
            r = _1865_recursiveGen;
          } else {
            RAST._IType _1869_rhsType;
            RAST._IType _out238;
            _out238 = (this).GenType(_1855_toTpe, DCOMP.GenTypeContext.InBinding());
            _1869_rhsType = _out238;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1869_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1865_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out239;
          DCOMP._IOwnership _out240;
          (this).FromOwnership(r, _1866_recOwned, expectedOwnership, out _out239, out _out240);
          r = _out239;
          resultingOwnership = _out240;
        }
      } else {
        if ((_1864_nativeToType).is_Some) {
          DAST._IType _source103 = _1854_fromTpe;
          bool unmatched103 = true;
          if (unmatched103) {
            if (_source103.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source103.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1870_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1871_range0 = kind1.dtor_range;
                bool _1872_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1873_attributes0 = resolved1.dtor_attributes;
                unmatched103 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1874_nativeFromType;
                  _1874_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1871_range0);
                  if ((_1874_nativeFromType).is_Some) {
                    RAST._IExpr _1875_recursiveGen;
                    DCOMP._IOwnership _1876_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1877_recIdents;
                    RAST._IExpr _out241;
                    DCOMP._IOwnership _out242;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out243;
                    (this).GenExpr(_1853_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out241, out _out242, out _out243);
                    _1875_recursiveGen = _out241;
                    _1876_recOwned = _out242;
                    _1877_recIdents = _out243;
                    RAST._IExpr _out244;
                    DCOMP._IOwnership _out245;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1875_recursiveGen, (_1864_nativeToType).dtor_value), _1876_recOwned, expectedOwnership, out _out244, out _out245);
                    r = _out244;
                    resultingOwnership = _out245;
                    readIdents = _1877_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched103) {
            unmatched103 = false;
          }
          if (object.Equals(_1854_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1878_recursiveGen;
            DCOMP._IOwnership _1879_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1880_recIdents;
            RAST._IExpr _out246;
            DCOMP._IOwnership _out247;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out248;
            (this).GenExpr(_1853_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out246, out _out247, out _out248);
            _1878_recursiveGen = _out246;
            _1879_recOwned = _out247;
            _1880_recIdents = _out248;
            RAST._IExpr _out249;
            DCOMP._IOwnership _out250;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1878_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1864_nativeToType).dtor_value), _1879_recOwned, expectedOwnership, out _out249, out _out250);
            r = _out249;
            resultingOwnership = _out250;
            readIdents = _1880_recIdents;
            return ;
          }
        }
        RAST._IExpr _out251;
        DCOMP._IOwnership _out252;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1853_expr, _1854_fromTpe, _1858_b), _1858_b, _1855_toTpe), selfIdent, env, expectedOwnership, out _out251, out _out252, out _out253);
        r = _out251;
        resultingOwnership = _out252;
        readIdents = _out253;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs59 = e;
      DAST._IExpression _1881_expr = _let_tmp_rhs59.dtor_value;
      DAST._IType _1882_fromTpe = _let_tmp_rhs59.dtor_from;
      DAST._IType _1883_toTpe = _let_tmp_rhs59.dtor_typ;
      DAST._IType _let_tmp_rhs60 = _1882_fromTpe;
      DAST._IResolvedType _let_tmp_rhs61 = _let_tmp_rhs60.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1884___v123 = _let_tmp_rhs61.dtor_path;
      Dafny.ISequence<DAST._IType> _1885___v124 = _let_tmp_rhs61.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs62 = _let_tmp_rhs61.dtor_kind;
      DAST._IType _1886_b = _let_tmp_rhs62.dtor_baseType;
      DAST._INewtypeRange _1887_range = _let_tmp_rhs62.dtor_range;
      bool _1888_erase = _let_tmp_rhs62.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1889_attributes = _let_tmp_rhs61.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1890___v125 = _let_tmp_rhs61.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1891___v126 = _let_tmp_rhs61.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1892_nativeFromType;
      _1892_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1887_range);
      if (object.Equals(_1886_b, _1883_toTpe)) {
        RAST._IExpr _1893_recursiveGen;
        DCOMP._IOwnership _1894_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1895_recIdents;
        RAST._IExpr _out254;
        DCOMP._IOwnership _out255;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out256;
        (this).GenExpr(_1881_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out254, out _out255, out _out256);
        _1893_recursiveGen = _out254;
        _1894_recOwned = _out255;
        _1895_recIdents = _out256;
        readIdents = _1895_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source104 = _1892_nativeFromType;
        bool unmatched104 = true;
        if (unmatched104) {
          if (_source104.is_Some) {
            RAST._IType _1896_v = _source104.dtor_value;
            unmatched104 = false;
            RAST._IType _1897_toTpeRust;
            RAST._IType _out257;
            _out257 = (this).GenType(_1883_toTpe, DCOMP.GenTypeContext.@default());
            _1897_toTpeRust = _out257;
            r = ((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1897_toTpeRust))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1893_recursiveGen));
            RAST._IExpr _out258;
            DCOMP._IOwnership _out259;
            (this).FromOwned(r, expectedOwnership, out _out258, out _out259);
            r = _out258;
            resultingOwnership = _out259;
          }
        }
        if (unmatched104) {
          unmatched104 = false;
          if (_1888_erase) {
            r = _1893_recursiveGen;
          } else {
            r = (_1893_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out260;
          DCOMP._IOwnership _out261;
          (this).FromOwnership(r, _1894_recOwned, expectedOwnership, out _out260, out _out261);
          r = _out260;
          resultingOwnership = _out261;
        }
      } else {
        if ((_1892_nativeFromType).is_Some) {
          if (object.Equals(_1883_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1898_recursiveGen;
            DCOMP._IOwnership _1899_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1900_recIdents;
            RAST._IExpr _out262;
            DCOMP._IOwnership _out263;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out264;
            (this).GenExpr(_1881_expr, selfIdent, env, expectedOwnership, out _out262, out _out263, out _out264);
            _1898_recursiveGen = _out262;
            _1899_recOwned = _out263;
            _1900_recIdents = _out264;
            RAST._IExpr _out265;
            DCOMP._IOwnership _out266;
            (this).FromOwnership((((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(RAST.Expr.create_TypeAscription(_1898_recursiveGen, (this).DafnyCharUnderlying)), _1899_recOwned, expectedOwnership, out _out265, out _out266);
            r = _out265;
            resultingOwnership = _out266;
            readIdents = _1900_recIdents;
            return ;
          }
        }
        RAST._IExpr _out267;
        DCOMP._IOwnership _out268;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out269;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1881_expr, _1882_fromTpe, _1886_b), _1886_b, _1883_toTpe), selfIdent, env, expectedOwnership, out _out267, out _out268, out _out269);
        r = _out267;
        resultingOwnership = _out268;
        readIdents = _out269;
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
        Std.Wrappers._IResult<__T, __E> _1901_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1901_valueOrError0).IsFailure()) {
          return (_1901_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1902_head = (_1901_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1903_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1903_valueOrError1).IsFailure()) {
            return (_1903_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1904_tail = (_1903_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1902_head), _1904_tail));
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
          RAST._IType _1905_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1906_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel((this).upcast)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1905_fromTpeUnderlying, _1906_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1907_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1907_valueOrError0).IsFailure()) {
          return (_1907_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1908_lambda = (_1907_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1908_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).AsExpr()).Apply1(_1908_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1909_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim13 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr13 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
          for (int i13 = 0; i13 < dim13; i13++) {
            var _1910_i = (BigInteger) i13;
            arr13[(int)(_1910_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_1910_i), ((fromTpe).dtor_arguments).Select(_1910_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_1910_i), ((toTpe).dtor_arguments).Select(_1910_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr13);
        }))());
        if ((_1909_valueOrError1).IsFailure()) {
          return (_1909_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1911_lambdas = (_1909_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim14 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr14 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim14, "array size exceeds memory limit")];
  for (int i14 = 0; i14 < dim14; i14++) {
    var _1912_i = (BigInteger) i14;
    arr14[(int)(_1912_i)] = ((fromTpe).dtor_arguments).Select(_1912_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr14);
}))())).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1911_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1913_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1914_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1915_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1916_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1917_valueOrError2 = (this).UpcastConversionLambda(_1915_newFromType, _1913_newFromTpe, _1916_newToType, _1914_newToTpe, typeParams);
        if ((_1917_valueOrError2).IsFailure()) {
          return (_1917_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1918_coerceArg = (_1917_valueOrError2).Extract();
          RAST._IPath _1919_collectionType = (RAST.__default.dafny__runtime).MSel(((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name);
          RAST._IExpr _1920_baseType = (((((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? (((_1919_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((((fromTpe).Expand()).dtor_arguments).Select(BigInteger.Zero), _1913_newFromTpe))) : (((_1919_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1913_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1920_baseType).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1918_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1921_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1921_valueOrError3).IsFailure()) {
          return (_1921_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1922_lambda = (_1921_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1922_lambda));
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
      DAST._IExpression _1923_expr = _let_tmp_rhs63.dtor_value;
      DAST._IType _1924_fromTpe = _let_tmp_rhs63.dtor_from;
      DAST._IType _1925_toTpe = _let_tmp_rhs63.dtor_typ;
      RAST._IType _1926_fromTpeGen;
      RAST._IType _out270;
      _out270 = (this).GenType(_1924_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1926_fromTpeGen = _out270;
      RAST._IType _1927_toTpeGen;
      RAST._IType _out271;
      _out271 = (this).GenType(_1925_toTpe, DCOMP.GenTypeContext.InBinding());
      _1927_toTpeGen = _out271;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1928_upcastConverter;
      _1928_upcastConverter = (this).UpcastConversionLambda(_1924_fromTpe, _1926_fromTpeGen, _1925_toTpe, _1927_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1928_upcastConverter).is_Success) {
        RAST._IExpr _1929_conversionLambda;
        _1929_conversionLambda = (_1928_upcastConverter).dtor_value;
        RAST._IExpr _1930_recursiveGen;
        DCOMP._IOwnership _1931_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1932_recIdents;
        RAST._IExpr _out272;
        DCOMP._IOwnership _out273;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out274;
        (this).GenExpr(_1923_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out272, out _out273, out _out274);
        _1930_recursiveGen = _out272;
        _1931_recOwned = _out273;
        _1932_recIdents = _out274;
        readIdents = _1932_recIdents;
        r = (_1929_conversionLambda).Apply1(_1930_recursiveGen);
        RAST._IExpr _out275;
        DCOMP._IOwnership _out276;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out275, out _out276);
        r = _out275;
        resultingOwnership = _out276;
      } else if ((this).IsDowncastConversion(_1926_fromTpeGen, _1927_toTpeGen)) {
        RAST._IExpr _1933_recursiveGen;
        DCOMP._IOwnership _1934_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1935_recIdents;
        RAST._IExpr _out277;
        DCOMP._IOwnership _out278;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out279;
        (this).GenExpr(_1923_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out277, out _out278, out _out279);
        _1933_recursiveGen = _out277;
        _1934_recOwned = _out278;
        _1935_recIdents = _out279;
        readIdents = _1935_recIdents;
        _1927_toTpeGen = (_1927_toTpeGen).ObjectOrPointerUnderlying();
        r = (((RAST.__default.dafny__runtime).MSel((this).downcast)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1933_recursiveGen, RAST.Expr.create_ExprFromType(_1927_toTpeGen)));
        RAST._IExpr _out280;
        DCOMP._IOwnership _out281;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out280, out _out281);
        r = _out280;
        resultingOwnership = _out281;
      } else {
        RAST._IExpr _1936_recursiveGen;
        DCOMP._IOwnership _1937_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1938_recIdents;
        RAST._IExpr _out282;
        DCOMP._IOwnership _out283;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out284;
        (this).GenExpr(_1923_expr, selfIdent, env, expectedOwnership, out _out282, out _out283, out _out284);
        _1936_recursiveGen = _out282;
        _1937_recOwned = _out283;
        _1938_recIdents = _out284;
        readIdents = _1938_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs64 = _1928_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs65 = _let_tmp_rhs64.dtor_error;
        DAST._IType _1939_fromType = _let_tmp_rhs65.dtor__0;
        RAST._IType _1940_fromTpeGen = _let_tmp_rhs65.dtor__1;
        DAST._IType _1941_toType = _let_tmp_rhs65.dtor__2;
        RAST._IType _1942_toTpeGen = _let_tmp_rhs65.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1943_m = _let_tmp_rhs65.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1944_msg;
        _1944_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1940_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1942_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1944_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1936_recursiveGen)._ToString(DCOMP.__default.IND), _1944_msg));
        RAST._IExpr _out285;
        DCOMP._IOwnership _out286;
        (this).FromOwnership(r, _1937_recOwned, expectedOwnership, out _out285, out _out286);
        r = _out285;
        resultingOwnership = _out286;
      }
    }
    public void GenExprConvert(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs66 = e;
      DAST._IExpression _1945_expr = _let_tmp_rhs66.dtor_value;
      DAST._IType _1946_fromTpe = _let_tmp_rhs66.dtor_from;
      DAST._IType _1947_toTpe = _let_tmp_rhs66.dtor_typ;
      if (object.Equals(_1946_fromTpe, _1947_toTpe)) {
        RAST._IExpr _1948_recursiveGen;
        DCOMP._IOwnership _1949_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1950_recIdents;
        RAST._IExpr _out287;
        DCOMP._IOwnership _out288;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out289;
        (this).GenExpr(_1945_expr, selfIdent, env, expectedOwnership, out _out287, out _out288, out _out289);
        _1948_recursiveGen = _out287;
        _1949_recOwned = _out288;
        _1950_recIdents = _out289;
        r = _1948_recursiveGen;
        RAST._IExpr _out290;
        DCOMP._IOwnership _out291;
        (this).FromOwnership(r, _1949_recOwned, expectedOwnership, out _out290, out _out291);
        r = _out290;
        resultingOwnership = _out291;
        readIdents = _1950_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source105 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1946_fromTpe, _1947_toTpe);
        bool unmatched105 = true;
        if (unmatched105) {
          DAST._IType _10 = _source105.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1951_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1952_range = kind2.dtor_range;
              bool _1953_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1954_attributes = resolved2.dtor_attributes;
              unmatched105 = false;
              {
                RAST._IExpr _out292;
                DCOMP._IOwnership _out293;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out292, out _out293, out _out294);
                r = _out292;
                resultingOwnership = _out293;
                readIdents = _out294;
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
              DAST._IType _1955_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1956_range = kind3.dtor_range;
              bool _1957_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1958_attributes = resolved3.dtor_attributes;
              unmatched105 = false;
              {
                RAST._IExpr _out295;
                DCOMP._IOwnership _out296;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out297;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out295, out _out296, out _out297);
                r = _out295;
                resultingOwnership = _out296;
                readIdents = _out297;
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
                    RAST._IExpr _1959_recursiveGen;
                    DCOMP._IOwnership _1960___v137;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1961_recIdents;
                    RAST._IExpr _out298;
                    DCOMP._IOwnership _out299;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out300;
                    (this).GenExpr(_1945_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out298, out _out299, out _out300);
                    _1959_recursiveGen = _out298;
                    _1960___v137 = _out299;
                    _1961_recIdents = _out300;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1959_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out301;
                    DCOMP._IOwnership _out302;
                    (this).FromOwned(r, expectedOwnership, out _out301, out _out302);
                    r = _out301;
                    resultingOwnership = _out302;
                    readIdents = _1961_recIdents;
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
                    RAST._IExpr _1962_recursiveGen;
                    DCOMP._IOwnership _1963___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1964_recIdents;
                    RAST._IExpr _out303;
                    DCOMP._IOwnership _out304;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out305;
                    (this).GenExpr(_1945_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out303, out _out304, out _out305);
                    _1962_recursiveGen = _out303;
                    _1963___v138 = _out304;
                    _1964_recIdents = _out305;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1962_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out306;
                    DCOMP._IOwnership _out307;
                    (this).FromOwned(r, expectedOwnership, out _out306, out _out307);
                    r = _out306;
                    resultingOwnership = _out307;
                    readIdents = _1964_recIdents;
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
                  RAST._IType _1965_rhsType;
                  RAST._IType _out308;
                  _out308 = (this).GenType(_1947_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1965_rhsType = _out308;
                  RAST._IExpr _1966_recursiveGen;
                  DCOMP._IOwnership _1967___v140;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1968_recIdents;
                  RAST._IExpr _out309;
                  DCOMP._IOwnership _out310;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out311;
                  (this).GenExpr(_1945_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out309, out _out310, out _out311);
                  _1966_recursiveGen = _out309;
                  _1967___v140 = _out310;
                  _1968_recIdents = _out311;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1965_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1966_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out312;
                  DCOMP._IOwnership _out313;
                  (this).FromOwned(r, expectedOwnership, out _out312, out _out313);
                  r = _out312;
                  resultingOwnership = _out313;
                  readIdents = _1968_recIdents;
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
                  RAST._IType _1969_rhsType;
                  RAST._IType _out314;
                  _out314 = (this).GenType(_1946_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1969_rhsType = _out314;
                  RAST._IExpr _1970_recursiveGen;
                  DCOMP._IOwnership _1971___v142;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1972_recIdents;
                  RAST._IExpr _out315;
                  DCOMP._IOwnership _out316;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out317;
                  (this).GenExpr(_1945_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out315, out _out316, out _out317);
                  _1970_recursiveGen = _out315;
                  _1971___v142 = _out316;
                  _1972_recIdents = _out317;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1970_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out318;
                  DCOMP._IOwnership _out319;
                  (this).FromOwned(r, expectedOwnership, out _out318, out _out319);
                  r = _out318;
                  resultingOwnership = _out319;
                  readIdents = _1972_recIdents;
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
                    RAST._IType _1973_rhsType;
                    RAST._IType _out320;
                    _out320 = (this).GenType(_1947_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1973_rhsType = _out320;
                    RAST._IExpr _1974_recursiveGen;
                    DCOMP._IOwnership _1975___v143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1976_recIdents;
                    RAST._IExpr _out321;
                    DCOMP._IOwnership _out322;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out323;
                    (this).GenExpr(_1945_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out321, out _out322, out _out323);
                    _1974_recursiveGen = _out321;
                    _1975___v143 = _out322;
                    _1976_recIdents = _out323;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1974_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out324;
                    DCOMP._IOwnership _out325;
                    (this).FromOwned(r, expectedOwnership, out _out324, out _out325);
                    r = _out324;
                    resultingOwnership = _out325;
                    readIdents = _1976_recIdents;
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
                    RAST._IType _1977_rhsType;
                    RAST._IType _out326;
                    _out326 = (this).GenType(_1946_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1977_rhsType = _out326;
                    RAST._IExpr _1978_recursiveGen;
                    DCOMP._IOwnership _1979___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1980_recIdents;
                    RAST._IExpr _out327;
                    DCOMP._IOwnership _out328;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out329;
                    (this).GenExpr(_1945_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out327, out _out328, out _out329);
                    _1978_recursiveGen = _out327;
                    _1979___v144 = _out328;
                    _1980_recIdents = _out329;
                    r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1((_1978_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out330;
                    DCOMP._IOwnership _out331;
                    (this).FromOwned(r, expectedOwnership, out _out330, out _out331);
                    r = _out330;
                    resultingOwnership = _out331;
                    readIdents = _1980_recIdents;
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
                RAST._IExpr _1981_recursiveGen;
                DCOMP._IOwnership _1982___v147;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1983_recIdents;
                RAST._IExpr _out332;
                DCOMP._IOwnership _out333;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out334;
                (this).GenExpr(_1945_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out332, out _out333, out _out334);
                _1981_recursiveGen = _out332;
                _1982___v147 = _out333;
                _1983_recIdents = _out334;
                RAST._IType _1984_toTpeGen;
                RAST._IType _out335;
                _out335 = (this).GenType(_1947_toTpe, DCOMP.GenTypeContext.InBinding());
                _1984_toTpeGen = _out335;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1981_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1984_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out336;
                DCOMP._IOwnership _out337;
                (this).FromOwned(r, expectedOwnership, out _out336, out _out337);
                r = _out336;
                resultingOwnership = _out337;
                readIdents = _1983_recIdents;
              }
            }
          }
        }
        if (unmatched105) {
          unmatched105 = false;
          {
            RAST._IExpr _out338;
            DCOMP._IOwnership _out339;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out340;
            (this).GenExprConvertOther(e, selfIdent, env, expectedOwnership, out _out338, out _out339, out _out340);
            r = _out338;
            resultingOwnership = _out339;
            readIdents = _out340;
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
      Std.Wrappers._IOption<RAST._IType> _1985_tpe;
      _1985_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1986_placeboOpt;
      _1986_placeboOpt = (((_1985_tpe).is_Some) ? (((_1985_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1987_currentlyBorrowed;
      _1987_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1988_noNeedOfClone;
      _1988_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1986_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1987_currentlyBorrowed = false;
        _1988_noNeedOfClone = true;
        _1985_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1986_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_1987_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1985_tpe).is_Some) && (((_1985_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1989_needObjectFromRef;
        _1989_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source106 = (selfIdent).dtor_dafnyType;
          bool unmatched106 = true;
          if (unmatched106) {
            if (_source106.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source106.dtor_resolved;
              DAST._IResolvedTypeBase _1990_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1991_attributes = resolved4.dtor_attributes;
              unmatched106 = false;
              return ((_1990_base).is_Class) || ((_1990_base).is_Trait);
            }
          }
          if (unmatched106) {
            unmatched106 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_1989_needObjectFromRef) {
          r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1988_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1988_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1987_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1985_tpe).is_Some) && (((_1985_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1992_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1992_attributes).UniqueElements, false, (((_exists_var_2) => {
        DAST._IAttribute _1993_attribute = (DAST._IAttribute)_exists_var_2;
        return ((_1992_attributes).Contains(_1993_attribute)) && ((((_1993_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1993_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      Dafny.ISequence<DAST._IFormal> _1994_signature;
      _1994_signature = (((name).is_CallName) ? ((((((name).dtor_receiverArg).is_Some) && ((name).dtor_receiverAsArgument)) ? (Dafny.Sequence<DAST._IFormal>.Concat(Dafny.Sequence<DAST._IFormal>.FromElements(((name).dtor_receiverArg).dtor_value), ((name).dtor_signature))) : (((name).dtor_signature)))) : (Dafny.Sequence<DAST._IFormal>.FromElements()));
      BigInteger _hi37 = new BigInteger((args).Count);
      for (BigInteger _1995_i = BigInteger.Zero; _1995_i < _hi37; _1995_i++) {
        DCOMP._IOwnership _1996_argOwnership;
        _1996_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if ((_1995_i) < (new BigInteger((_1994_signature).Count))) {
          RAST._IType _1997_tpe;
          RAST._IType _out341;
          _out341 = (this).GenType(((_1994_signature).Select(_1995_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1997_tpe = _out341;
          if ((_1997_tpe).CanReadWithoutClone()) {
            _1996_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1998_argExpr;
        DCOMP._IOwnership _1999___v154;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2000_argIdents;
        RAST._IExpr _out342;
        DCOMP._IOwnership _out343;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out344;
        (this).GenExpr((args).Select(_1995_i), selfIdent, env, _1996_argOwnership, out _out342, out _out343, out _out344);
        _1998_argExpr = _out342;
        _1999___v154 = _out343;
        _2000_argIdents = _out344;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1998_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2000_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi38 = new BigInteger((typeArgs).Count);
      for (BigInteger _2001_typeI = BigInteger.Zero; _2001_typeI < _hi38; _2001_typeI++) {
        RAST._IType _2002_typeExpr;
        RAST._IType _out345;
        _out345 = (this).GenType((typeArgs).Select(_2001_typeI), DCOMP.GenTypeContext.@default());
        _2002_typeExpr = _out345;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2002_typeExpr));
      }
      DAST._ICallName _source107 = name;
      bool unmatched107 = true;
      if (unmatched107) {
        if (_source107.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _2003_nameIdent = _source107.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType1 = _source107.dtor_onType;
          if (onType1.is_Some) {
            DAST._IType value10 = onType1.dtor_value;
            if (value10.is_UserDefined) {
              DAST._IResolvedType _2004_resolvedType = value10.dtor_resolved;
              unmatched107 = false;
              if ((((_2004_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_2005_resolvedType, _2006_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.SingleValue<Dafny.ISequence<Dafny.Rune>>(_2006_nameIdent), true, (((_forall_var_8) => {
                Dafny.ISequence<Dafny.Rune> _2007_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                return !(((_2005_resolvedType).dtor_properMethods).Contains(_2007_m)) || (!object.Equals(_2007_m, _2006_nameIdent));
              }))))(_2004_resolvedType, _2003_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_2004_resolvedType, (_2003_nameIdent)), _2004_resolvedType));
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
      var _pat_let_tv201 = @on;
      DAST._ICallName _source108 = name;
      bool unmatched108 = true;
      if (unmatched108) {
        if (_source108.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _2008_ident = _source108.dtor_name;
          unmatched108 = false;
          if ((_pat_let_tv201).is_ExternCompanion) {
            return (_2008_ident);
          } else {
            return DCOMP.__default.escapeName(_2008_ident);
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
          RAST._IExpr _out346;
          DCOMP._IOwnership _out347;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out346, out _out347, out _out348);
          r = _out346;
          resultingOwnership = _out347;
          readIdents = _out348;
        }
      }
      if (unmatched109) {
        if (_source109.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _2009_name = _source109.dtor_name;
          unmatched109 = false;
          {
            RAST._IExpr _out349;
            DCOMP._IOwnership _out350;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out351;
            (this).GenIdent(DCOMP.__default.escapeVar(_2009_name), selfIdent, env, expectedOwnership, out _out349, out _out350, out _out351);
            r = _out349;
            resultingOwnership = _out350;
            readIdents = _out351;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_ExternCompanion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2010_path = _source109.dtor_ExternCompanion_a0;
          unmatched109 = false;
          {
            RAST._IExpr _out352;
            _out352 = DCOMP.COMP.GenPathExpr(_2010_path, false);
            r = _out352;
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out353;
              DCOMP._IOwnership _out354;
              (this).FromOwned(r, expectedOwnership, out _out353, out _out354);
              r = _out353;
              resultingOwnership = _out354;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2011_path = _source109.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _2012_typeArgs = _source109.dtor_typeArgs;
          unmatched109 = false;
          {
            RAST._IExpr _out355;
            _out355 = DCOMP.COMP.GenPathExpr(_2011_path, true);
            r = _out355;
            if ((new BigInteger((_2012_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _2013_typeExprs;
              _2013_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi39 = new BigInteger((_2012_typeArgs).Count);
              for (BigInteger _2014_i = BigInteger.Zero; _2014_i < _hi39; _2014_i++) {
                RAST._IType _2015_typeExpr;
                RAST._IType _out356;
                _out356 = (this).GenType((_2012_typeArgs).Select(_2014_i), DCOMP.GenTypeContext.@default());
                _2015_typeExpr = _out356;
                _2013_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_2013_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2015_typeExpr));
              }
              r = (r).ApplyType(_2013_typeExprs);
            }
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out357;
              DCOMP._IOwnership _out358;
              (this).FromOwned(r, expectedOwnership, out _out357, out _out358);
              r = _out357;
              resultingOwnership = _out358;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_InitializationValue) {
          DAST._IType _2016_typ = _source109.dtor_typ;
          unmatched109 = false;
          {
            RAST._IType _2017_typExpr;
            RAST._IType _out359;
            _out359 = (this).GenType(_2016_typ, DCOMP.GenTypeContext.@default());
            _2017_typExpr = _out359;
            if ((_2017_typExpr).IsObjectOrPointer()) {
              r = (_2017_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_2017_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            }
            RAST._IExpr _out360;
            DCOMP._IOwnership _out361;
            (this).FromOwned(r, expectedOwnership, out _out360, out _out361);
            r = _out360;
            resultingOwnership = _out361;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _2018_values = _source109.dtor_Tuple_a0;
          unmatched109 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2019_exprs;
            _2019_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi40 = new BigInteger((_2018_values).Count);
            for (BigInteger _2020_i = BigInteger.Zero; _2020_i < _hi40; _2020_i++) {
              RAST._IExpr _2021_recursiveGen;
              DCOMP._IOwnership _2022___v164;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2023_recIdents;
              RAST._IExpr _out362;
              DCOMP._IOwnership _out363;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out364;
              (this).GenExpr((_2018_values).Select(_2020_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out362, out _out363, out _out364);
              _2021_recursiveGen = _out362;
              _2022___v164 = _out363;
              _2023_recIdents = _out364;
              _2019_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_2019_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2021_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2023_recIdents);
            }
            r = (((new BigInteger((_2018_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_2019_exprs)) : (RAST.__default.SystemTuple(_2019_exprs)));
            RAST._IExpr _out365;
            DCOMP._IOwnership _out366;
            (this).FromOwned(r, expectedOwnership, out _out365, out _out366);
            r = _out365;
            resultingOwnership = _out366;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2024_path = _source109.dtor_path;
          Dafny.ISequence<DAST._IType> _2025_typeArgs = _source109.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2026_args = _source109.dtor_args;
          unmatched109 = false;
          {
            RAST._IExpr _out367;
            _out367 = DCOMP.COMP.GenPathExpr(_2024_path, true);
            r = _out367;
            if ((new BigInteger((_2025_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _2027_typeExprs;
              _2027_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi41 = new BigInteger((_2025_typeArgs).Count);
              for (BigInteger _2028_i = BigInteger.Zero; _2028_i < _hi41; _2028_i++) {
                RAST._IType _2029_typeExpr;
                RAST._IType _out368;
                _out368 = (this).GenType((_2025_typeArgs).Select(_2028_i), DCOMP.GenTypeContext.@default());
                _2029_typeExpr = _out368;
                _2027_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_2027_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2029_typeExpr));
              }
              r = (r).ApplyType(_2027_typeExprs);
            }
            r = (r).FSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _2030_arguments;
            _2030_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi42 = new BigInteger((_2026_args).Count);
            for (BigInteger _2031_i = BigInteger.Zero; _2031_i < _hi42; _2031_i++) {
              RAST._IExpr _2032_recursiveGen;
              DCOMP._IOwnership _2033___v165;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2034_recIdents;
              RAST._IExpr _out369;
              DCOMP._IOwnership _out370;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
              (this).GenExpr((_2026_args).Select(_2031_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out369, out _out370, out _out371);
              _2032_recursiveGen = _out369;
              _2033___v165 = _out370;
              _2034_recIdents = _out371;
              _2030_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2030_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2032_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2034_recIdents);
            }
            r = (r).Apply(_2030_arguments);
            RAST._IExpr _out372;
            DCOMP._IOwnership _out373;
            (this).FromOwned(r, expectedOwnership, out _out372, out _out373);
            r = _out372;
            resultingOwnership = _out373;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _2035_dims = _source109.dtor_dims;
          DAST._IType _2036_typ = _source109.dtor_typ;
          unmatched109 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_2035_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _2037_msg;
              _2037_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2037_msg);
              }
              r = RAST.Expr.create_RawExpr(_2037_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _2038_typeGen;
              RAST._IType _out374;
              _out374 = (this).GenType(_2036_typ, DCOMP.GenTypeContext.@default());
              _2038_typeGen = _out374;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _2039_dimExprs;
              _2039_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi43 = new BigInteger((_2035_dims).Count);
              for (BigInteger _2040_i = BigInteger.Zero; _2040_i < _hi43; _2040_i++) {
                RAST._IExpr _2041_recursiveGen;
                DCOMP._IOwnership _2042___v166;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2043_recIdents;
                RAST._IExpr _out375;
                DCOMP._IOwnership _out376;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out377;
                (this).GenExpr((_2035_dims).Select(_2040_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out375, out _out376, out _out377);
                _2041_recursiveGen = _out375;
                _2042___v166 = _out376;
                _2043_recIdents = _out377;
                _2039_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_2039_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_2041_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2043_recIdents);
              }
              if ((new BigInteger((_2035_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _2044_class__name;
                _2044_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_2035_dims).Count)));
                r = (((((RAST.__default.dafny__runtime).MSel(_2044_class__name)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2038_typeGen))).FSel((this).placebos__usize)).Apply(_2039_dimExprs);
              } else {
                r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2038_typeGen))).Apply(_2039_dimExprs);
              }
            }
            RAST._IExpr _out378;
            DCOMP._IOwnership _out379;
            (this).FromOwned(r, expectedOwnership, out _out378, out _out379);
            r = _out378;
            resultingOwnership = _out379;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_ArrayIndexToInt) {
          DAST._IExpression _2045_underlying = _source109.dtor_value;
          unmatched109 = false;
          {
            RAST._IExpr _2046_recursiveGen;
            DCOMP._IOwnership _2047___v167;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2048_recIdents;
            RAST._IExpr _out380;
            DCOMP._IOwnership _out381;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
            (this).GenExpr(_2045_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out380, out _out381, out _out382);
            _2046_recursiveGen = _out380;
            _2047___v167 = _out381;
            _2048_recIdents = _out382;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(_2046_recursiveGen);
            readIdents = _2048_recIdents;
            RAST._IExpr _out383;
            DCOMP._IOwnership _out384;
            (this).FromOwned(r, expectedOwnership, out _out383, out _out384);
            r = _out383;
            resultingOwnership = _out384;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_FinalizeNewArray) {
          DAST._IExpression _2049_underlying = _source109.dtor_value;
          DAST._IType _2050_typ = _source109.dtor_typ;
          unmatched109 = false;
          {
            RAST._IType _2051_tpe;
            RAST._IType _out385;
            _out385 = (this).GenType(_2050_typ, DCOMP.GenTypeContext.@default());
            _2051_tpe = _out385;
            RAST._IExpr _2052_recursiveGen;
            DCOMP._IOwnership _2053___v168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2054_recIdents;
            RAST._IExpr _out386;
            DCOMP._IOwnership _out387;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out388;
            (this).GenExpr(_2049_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out386, out _out387, out _out388);
            _2052_recursiveGen = _out386;
            _2053___v168 = _out387;
            _2054_recIdents = _out388;
            readIdents = _2054_recIdents;
            if ((_2051_tpe).IsObjectOrPointer()) {
              RAST._IType _2055_t;
              _2055_t = (_2051_tpe).ObjectOrPointerUnderlying();
              if ((_2055_t).is_Array) {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).array__construct)).Apply1(_2052_recursiveGen);
              } else if ((_2055_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _2056_c;
                _2056_c = (_2055_t).MultiArrayClass();
                r = ((((RAST.__default.dafny__runtime).MSel(_2056_c)).AsExpr()).FSel((this).array__construct)).Apply1(_2052_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_2051_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_2051_tpe)._ToString(DCOMP.__default.IND)));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            }
            RAST._IExpr _out389;
            DCOMP._IOwnership _out390;
            (this).FromOwned(r, expectedOwnership, out _out389, out _out390);
            r = _out389;
            resultingOwnership = _out390;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_DatatypeValue) {
          DAST._IResolvedType _2057_datatypeType = _source109.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _2058_typeArgs = _source109.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _2059_variant = _source109.dtor_variant;
          bool _2060_isCo = _source109.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2061_values = _source109.dtor_contents;
          unmatched109 = false;
          {
            RAST._IExpr _out391;
            _out391 = DCOMP.COMP.GenPathExpr((_2057_datatypeType).dtor_path, true);
            r = _out391;
            Dafny.ISequence<RAST._IType> _2062_genTypeArgs;
            _2062_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi44 = new BigInteger((_2058_typeArgs).Count);
            for (BigInteger _2063_i = BigInteger.Zero; _2063_i < _hi44; _2063_i++) {
              RAST._IType _2064_typeExpr;
              RAST._IType _out392;
              _out392 = (this).GenType((_2058_typeArgs).Select(_2063_i), DCOMP.GenTypeContext.@default());
              _2064_typeExpr = _out392;
              _2062_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_2062_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_2064_typeExpr));
            }
            if ((new BigInteger((_2058_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_2062_genTypeArgs);
            }
            r = (r).FSel(DCOMP.__default.escapeName(_2059_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _2065_assignments;
            _2065_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi45 = new BigInteger((_2061_values).Count);
            for (BigInteger _2066_i = BigInteger.Zero; _2066_i < _hi45; _2066_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs67 = (_2061_values).Select(_2066_i);
              Dafny.ISequence<Dafny.Rune> _2067_name = _let_tmp_rhs67.dtor__0;
              DAST._IExpression _2068_value = _let_tmp_rhs67.dtor__1;
              if (_2060_isCo) {
                RAST._IExpr _2069_recursiveGen;
                DCOMP._IOwnership _2070___v169;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2071_recIdents;
                RAST._IExpr _out393;
                DCOMP._IOwnership _out394;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
                (this).GenExpr(_2068_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out393, out _out394, out _out395);
                _2069_recursiveGen = _out393;
                _2070___v169 = _out394;
                _2071_recIdents = _out395;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2071_recIdents);
                Dafny.ISequence<Dafny.Rune> _2072_allReadCloned;
                _2072_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_2071_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _2073_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2071_recIdents).Elements) {
                    _2073_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                    if ((_2071_recIdents).Contains(_2073_next)) {
                      goto after__ASSIGN_SUCH_THAT_3;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4696)");
                after__ASSIGN_SUCH_THAT_3: ;
                  _2072_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2072_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _2073_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2073_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _2071_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2071_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2073_next));
                }
                Dafny.ISequence<Dafny.Rune> _2074_wasAssigned;
                _2074_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _2072_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_2069_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _2065_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2065_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_2067_name), RAST.Expr.create_RawExpr(_2074_wasAssigned))));
              } else {
                RAST._IExpr _2075_recursiveGen;
                DCOMP._IOwnership _2076___v170;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2077_recIdents;
                RAST._IExpr _out396;
                DCOMP._IOwnership _out397;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out398;
                (this).GenExpr(_2068_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out396, out _out397, out _out398);
                _2075_recursiveGen = _out396;
                _2076___v170 = _out397;
                _2077_recIdents = _out398;
                _2065_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2065_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_2067_name), _2075_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2077_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _2065_assignments);
            if ((this).IsRcWrapped((_2057_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out399;
            DCOMP._IOwnership _out400;
            (this).FromOwned(r, expectedOwnership, out _out399, out _out400);
            r = _out399;
            resultingOwnership = _out400;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Convert) {
          unmatched109 = false;
          {
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out401, out _out402, out _out403);
            r = _out401;
            resultingOwnership = _out402;
            readIdents = _out403;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SeqConstruct) {
          DAST._IExpression _2078_length = _source109.dtor_length;
          DAST._IExpression _2079_expr = _source109.dtor_elem;
          unmatched109 = false;
          {
            RAST._IExpr _2080_recursiveGen;
            DCOMP._IOwnership _2081___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2082_recIdents;
            RAST._IExpr _out404;
            DCOMP._IOwnership _out405;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out406;
            (this).GenExpr(_2079_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out404, out _out405, out _out406);
            _2080_recursiveGen = _out404;
            _2081___v174 = _out405;
            _2082_recIdents = _out406;
            RAST._IExpr _2083_lengthGen;
            DCOMP._IOwnership _2084___v175;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2085_lengthIdents;
            RAST._IExpr _out407;
            DCOMP._IOwnership _out408;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
            (this).GenExpr(_2078_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out407, out _out408, out _out409);
            _2083_lengthGen = _out407;
            _2084___v175 = _out408;
            _2085_lengthIdents = _out409;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_2080_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_2083_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2082_recIdents, _2085_lengthIdents);
            RAST._IExpr _out410;
            DCOMP._IOwnership _out411;
            (this).FromOwned(r, expectedOwnership, out _out410, out _out411);
            r = _out410;
            resultingOwnership = _out411;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _2086_exprs = _source109.dtor_elements;
          DAST._IType _2087_typ = _source109.dtor_typ;
          unmatched109 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _2088_genTpe;
            RAST._IType _out412;
            _out412 = (this).GenType(_2087_typ, DCOMP.GenTypeContext.@default());
            _2088_genTpe = _out412;
            BigInteger _2089_i;
            _2089_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2090_args;
            _2090_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2089_i) < (new BigInteger((_2086_exprs).Count))) {
              RAST._IExpr _2091_recursiveGen;
              DCOMP._IOwnership _2092___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2093_recIdents;
              RAST._IExpr _out413;
              DCOMP._IOwnership _out414;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
              (this).GenExpr((_2086_exprs).Select(_2089_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out413, out _out414, out _out415);
              _2091_recursiveGen = _out413;
              _2092___v176 = _out414;
              _2093_recIdents = _out415;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2093_recIdents);
              _2090_args = Dafny.Sequence<RAST._IExpr>.Concat(_2090_args, Dafny.Sequence<RAST._IExpr>.FromElements(_2091_recursiveGen));
              _2089_i = (_2089_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).AsExpr()).Apply(_2090_args);
            if ((new BigInteger((_2090_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType()).Apply1(_2088_genTpe));
            }
            RAST._IExpr _out416;
            DCOMP._IOwnership _out417;
            (this).FromOwned(r, expectedOwnership, out _out416, out _out417);
            r = _out416;
            resultingOwnership = _out417;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _2094_exprs = _source109.dtor_elements;
          unmatched109 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2095_generatedValues;
            _2095_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2096_i;
            _2096_i = BigInteger.Zero;
            while ((_2096_i) < (new BigInteger((_2094_exprs).Count))) {
              RAST._IExpr _2097_recursiveGen;
              DCOMP._IOwnership _2098___v177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2099_recIdents;
              RAST._IExpr _out418;
              DCOMP._IOwnership _out419;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out420;
              (this).GenExpr((_2094_exprs).Select(_2096_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out418, out _out419, out _out420);
              _2097_recursiveGen = _out418;
              _2098___v177 = _out419;
              _2099_recIdents = _out420;
              _2095_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2095_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2097_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2099_recIdents);
              _2096_i = (_2096_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).AsExpr()).Apply(_2095_generatedValues);
            RAST._IExpr _out421;
            DCOMP._IOwnership _out422;
            (this).FromOwned(r, expectedOwnership, out _out421, out _out422);
            r = _out421;
            resultingOwnership = _out422;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _2100_exprs = _source109.dtor_elements;
          unmatched109 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2101_generatedValues;
            _2101_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2102_i;
            _2102_i = BigInteger.Zero;
            while ((_2102_i) < (new BigInteger((_2100_exprs).Count))) {
              RAST._IExpr _2103_recursiveGen;
              DCOMP._IOwnership _2104___v178;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2105_recIdents;
              RAST._IExpr _out423;
              DCOMP._IOwnership _out424;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out425;
              (this).GenExpr((_2100_exprs).Select(_2102_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out423, out _out424, out _out425);
              _2103_recursiveGen = _out423;
              _2104___v178 = _out424;
              _2105_recIdents = _out425;
              _2101_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2101_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2103_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2105_recIdents);
              _2102_i = (_2102_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).AsExpr()).Apply(_2101_generatedValues);
            RAST._IExpr _out426;
            DCOMP._IOwnership _out427;
            (this).FromOwned(r, expectedOwnership, out _out426, out _out427);
            r = _out426;
            resultingOwnership = _out427;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_ToMultiset) {
          DAST._IExpression _2106_expr = _source109.dtor_ToMultiset_a0;
          unmatched109 = false;
          {
            RAST._IExpr _2107_recursiveGen;
            DCOMP._IOwnership _2108___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2109_recIdents;
            RAST._IExpr _out428;
            DCOMP._IOwnership _out429;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out430;
            (this).GenExpr(_2106_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out428, out _out429, out _out430);
            _2107_recursiveGen = _out428;
            _2108___v179 = _out429;
            _2109_recIdents = _out430;
            r = ((_2107_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2109_recIdents;
            RAST._IExpr _out431;
            DCOMP._IOwnership _out432;
            (this).FromOwned(r, expectedOwnership, out _out431, out _out432);
            r = _out431;
            resultingOwnership = _out432;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2110_mapElems = _source109.dtor_mapElems;
          unmatched109 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _2111_generatedValues;
            _2111_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2112_i;
            _2112_i = BigInteger.Zero;
            while ((_2112_i) < (new BigInteger((_2110_mapElems).Count))) {
              RAST._IExpr _2113_recursiveGenKey;
              DCOMP._IOwnership _2114___v180;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2115_recIdentsKey;
              RAST._IExpr _out433;
              DCOMP._IOwnership _out434;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out435;
              (this).GenExpr(((_2110_mapElems).Select(_2112_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out433, out _out434, out _out435);
              _2113_recursiveGenKey = _out433;
              _2114___v180 = _out434;
              _2115_recIdentsKey = _out435;
              RAST._IExpr _2116_recursiveGenValue;
              DCOMP._IOwnership _2117___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2118_recIdentsValue;
              RAST._IExpr _out436;
              DCOMP._IOwnership _out437;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out438;
              (this).GenExpr(((_2110_mapElems).Select(_2112_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out436, out _out437, out _out438);
              _2116_recursiveGenValue = _out436;
              _2117___v181 = _out437;
              _2118_recIdentsValue = _out438;
              _2111_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_2111_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_2113_recursiveGenKey, _2116_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2115_recIdentsKey), _2118_recIdentsValue);
              _2112_i = (_2112_i) + (BigInteger.One);
            }
            _2112_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2119_arguments;
            _2119_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2112_i) < (new BigInteger((_2111_generatedValues).Count))) {
              RAST._IExpr _2120_genKey;
              _2120_genKey = ((_2111_generatedValues).Select(_2112_i)).dtor__0;
              RAST._IExpr _2121_genValue;
              _2121_genValue = ((_2111_generatedValues).Select(_2112_i)).dtor__1;
              _2119_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2119_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _2120_genKey, _2121_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _2112_i = (_2112_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).AsExpr()).Apply(_2119_arguments);
            RAST._IExpr _out439;
            DCOMP._IOwnership _out440;
            (this).FromOwned(r, expectedOwnership, out _out439, out _out440);
            r = _out439;
            resultingOwnership = _out440;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SeqUpdate) {
          DAST._IExpression _2122_expr = _source109.dtor_expr;
          DAST._IExpression _2123_index = _source109.dtor_indexExpr;
          DAST._IExpression _2124_value = _source109.dtor_value;
          unmatched109 = false;
          {
            RAST._IExpr _2125_exprR;
            DCOMP._IOwnership _2126___v182;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2127_exprIdents;
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
            (this).GenExpr(_2122_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out441, out _out442, out _out443);
            _2125_exprR = _out441;
            _2126___v182 = _out442;
            _2127_exprIdents = _out443;
            RAST._IExpr _2128_indexR;
            DCOMP._IOwnership _2129_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2130_indexIdents;
            RAST._IExpr _out444;
            DCOMP._IOwnership _out445;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out446;
            (this).GenExpr(_2123_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out444, out _out445, out _out446);
            _2128_indexR = _out444;
            _2129_indexOwnership = _out445;
            _2130_indexIdents = _out446;
            RAST._IExpr _2131_valueR;
            DCOMP._IOwnership _2132_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2133_valueIdents;
            RAST._IExpr _out447;
            DCOMP._IOwnership _out448;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out449;
            (this).GenExpr(_2124_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out447, out _out448, out _out449);
            _2131_valueR = _out447;
            _2132_valueOwnership = _out448;
            _2133_valueIdents = _out449;
            r = ((_2125_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2128_indexR, _2131_valueR));
            RAST._IExpr _out450;
            DCOMP._IOwnership _out451;
            (this).FromOwned(r, expectedOwnership, out _out450, out _out451);
            r = _out450;
            resultingOwnership = _out451;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2127_exprIdents, _2130_indexIdents), _2133_valueIdents);
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapUpdate) {
          DAST._IExpression _2134_expr = _source109.dtor_expr;
          DAST._IExpression _2135_index = _source109.dtor_indexExpr;
          DAST._IExpression _2136_value = _source109.dtor_value;
          unmatched109 = false;
          {
            RAST._IExpr _2137_exprR;
            DCOMP._IOwnership _2138___v183;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2139_exprIdents;
            RAST._IExpr _out452;
            DCOMP._IOwnership _out453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
            (this).GenExpr(_2134_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out452, out _out453, out _out454);
            _2137_exprR = _out452;
            _2138___v183 = _out453;
            _2139_exprIdents = _out454;
            RAST._IExpr _2140_indexR;
            DCOMP._IOwnership _2141_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2142_indexIdents;
            RAST._IExpr _out455;
            DCOMP._IOwnership _out456;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out457;
            (this).GenExpr(_2135_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out455, out _out456, out _out457);
            _2140_indexR = _out455;
            _2141_indexOwnership = _out456;
            _2142_indexIdents = _out457;
            RAST._IExpr _2143_valueR;
            DCOMP._IOwnership _2144_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2145_valueIdents;
            RAST._IExpr _out458;
            DCOMP._IOwnership _out459;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
            (this).GenExpr(_2136_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out458, out _out459, out _out460);
            _2143_valueR = _out458;
            _2144_valueOwnership = _out459;
            _2145_valueIdents = _out460;
            r = ((_2137_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2140_indexR, _2143_valueR));
            RAST._IExpr _out461;
            DCOMP._IOwnership _out462;
            (this).FromOwned(r, expectedOwnership, out _out461, out _out462);
            r = _out461;
            resultingOwnership = _out462;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2139_exprIdents, _2142_indexIdents), _2145_valueIdents);
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
                Dafny.ISequence<Dafny.Rune> _2146_id = _source110.dtor_rSelfName;
                DAST._IType _2147_dafnyType = _source110.dtor_dafnyType;
                unmatched110 = false;
                {
                  RAST._IExpr _out463;
                  DCOMP._IOwnership _out464;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out465;
                  (this).GenIdent(_2146_id, selfIdent, env, expectedOwnership, out _out463, out _out464, out _out465);
                  r = _out463;
                  resultingOwnership = _out464;
                  readIdents = _out465;
                }
              }
            }
            if (unmatched110) {
              DCOMP._ISelfInfo _2148_None = _source110;
              unmatched110 = false;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out466;
                DCOMP._IOwnership _out467;
                (this).FromOwned(r, expectedOwnership, out _out466, out _out467);
                r = _out466;
                resultingOwnership = _out467;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Ite) {
          DAST._IExpression _2149_cond = _source109.dtor_cond;
          DAST._IExpression _2150_t = _source109.dtor_thn;
          DAST._IExpression _2151_f = _source109.dtor_els;
          unmatched109 = false;
          {
            RAST._IExpr _2152_cond;
            DCOMP._IOwnership _2153___v184;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2154_recIdentsCond;
            RAST._IExpr _out468;
            DCOMP._IOwnership _out469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out470;
            (this).GenExpr(_2149_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out468, out _out469, out _out470);
            _2152_cond = _out468;
            _2153___v184 = _out469;
            _2154_recIdentsCond = _out470;
            RAST._IExpr _2155_fExpr;
            DCOMP._IOwnership _2156_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2157_recIdentsF;
            RAST._IExpr _out471;
            DCOMP._IOwnership _out472;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out473;
            (this).GenExpr(_2151_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out471, out _out472, out _out473);
            _2155_fExpr = _out471;
            _2156_fOwned = _out472;
            _2157_recIdentsF = _out473;
            RAST._IExpr _2158_tExpr;
            DCOMP._IOwnership _2159___v185;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2160_recIdentsT;
            RAST._IExpr _out474;
            DCOMP._IOwnership _out475;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out476;
            (this).GenExpr(_2150_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out474, out _out475, out _out476);
            _2158_tExpr = _out474;
            _2159___v185 = _out475;
            _2160_recIdentsT = _out476;
            r = RAST.Expr.create_IfExpr(_2152_cond, _2158_tExpr, _2155_fExpr);
            RAST._IExpr _out477;
            DCOMP._IOwnership _out478;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out477, out _out478);
            r = _out477;
            resultingOwnership = _out478;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2154_recIdentsCond, _2160_recIdentsT), _2157_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source109.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _2161_e = _source109.dtor_expr;
            DAST.Format._IUnaryOpFormat _2162_format = _source109.dtor_format1;
            unmatched109 = false;
            {
              RAST._IExpr _2163_recursiveGen;
              DCOMP._IOwnership _2164___v186;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2165_recIdents;
              RAST._IExpr _out479;
              DCOMP._IOwnership _out480;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out481;
              (this).GenExpr(_2161_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out479, out _out480, out _out481);
              _2163_recursiveGen = _out479;
              _2164___v186 = _out480;
              _2165_recIdents = _out481;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _2163_recursiveGen, _2162_format);
              RAST._IExpr _out482;
              DCOMP._IOwnership _out483;
              (this).FromOwned(r, expectedOwnership, out _out482, out _out483);
              r = _out482;
              resultingOwnership = _out483;
              readIdents = _2165_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source109.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _2166_e = _source109.dtor_expr;
            DAST.Format._IUnaryOpFormat _2167_format = _source109.dtor_format1;
            unmatched109 = false;
            {
              RAST._IExpr _2168_recursiveGen;
              DCOMP._IOwnership _2169___v187;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2170_recIdents;
              RAST._IExpr _out484;
              DCOMP._IOwnership _out485;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out486;
              (this).GenExpr(_2166_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out484, out _out485, out _out486);
              _2168_recursiveGen = _out484;
              _2169___v187 = _out485;
              _2170_recIdents = _out486;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _2168_recursiveGen, _2167_format);
              RAST._IExpr _out487;
              DCOMP._IOwnership _out488;
              (this).FromOwned(r, expectedOwnership, out _out487, out _out488);
              r = _out487;
              resultingOwnership = _out488;
              readIdents = _2170_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source109.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _2171_e = _source109.dtor_expr;
            DAST.Format._IUnaryOpFormat _2172_format = _source109.dtor_format1;
            unmatched109 = false;
            {
              RAST._IExpr _2173_recursiveGen;
              DCOMP._IOwnership _2174_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2175_recIdents;
              RAST._IExpr _out489;
              DCOMP._IOwnership _out490;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out491;
              (this).GenExpr(_2171_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out489, out _out490, out _out491);
              _2173_recursiveGen = _out489;
              _2174_recOwned = _out490;
              _2175_recIdents = _out491;
              r = ((_2173_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out492;
              DCOMP._IOwnership _out493;
              (this).FromOwned(r, expectedOwnership, out _out492, out _out493);
              r = _out492;
              resultingOwnership = _out493;
              readIdents = _2175_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_BinOp) {
          unmatched109 = false;
          RAST._IExpr _out494;
          DCOMP._IOwnership _out495;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out494, out _out495, out _out496);
          r = _out494;
          resultingOwnership = _out495;
          readIdents = _out496;
        }
      }
      if (unmatched109) {
        if (_source109.is_ArrayLen) {
          DAST._IExpression _2176_expr = _source109.dtor_expr;
          DAST._IType _2177_exprType = _source109.dtor_exprType;
          BigInteger _2178_dim = _source109.dtor_dim;
          bool _2179_native = _source109.dtor_native;
          unmatched109 = false;
          {
            RAST._IExpr _2180_recursiveGen;
            DCOMP._IOwnership _2181___v192;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2182_recIdents;
            RAST._IExpr _out497;
            DCOMP._IOwnership _out498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
            (this).GenExpr(_2176_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out497, out _out498, out _out499);
            _2180_recursiveGen = _out497;
            _2181___v192 = _out498;
            _2182_recIdents = _out499;
            RAST._IType _2183_arrayType;
            RAST._IType _out500;
            _out500 = (this).GenType(_2177_exprType, DCOMP.GenTypeContext.@default());
            _2183_arrayType = _out500;
            if (!((_2183_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2184_msg;
              _2184_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2183_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2184_msg);
              r = RAST.Expr.create_RawExpr(_2184_msg);
            } else {
              RAST._IType _2185_underlying;
              _2185_underlying = (_2183_arrayType).ObjectOrPointerUnderlying();
              if (((_2178_dim).Sign == 0) && ((_2185_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2180_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2178_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2180_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_2180_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_2178_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_2179_native)) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(r);
              }
            }
            RAST._IExpr _out501;
            DCOMP._IOwnership _out502;
            (this).FromOwned(r, expectedOwnership, out _out501, out _out502);
            r = _out501;
            resultingOwnership = _out502;
            readIdents = _2182_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapKeys) {
          DAST._IExpression _2186_expr = _source109.dtor_expr;
          unmatched109 = false;
          {
            RAST._IExpr _2187_recursiveGen;
            DCOMP._IOwnership _2188___v193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2189_recIdents;
            RAST._IExpr _out503;
            DCOMP._IOwnership _out504;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
            (this).GenExpr(_2186_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out503, out _out504, out _out505);
            _2187_recursiveGen = _out503;
            _2188___v193 = _out504;
            _2189_recIdents = _out505;
            readIdents = _2189_recIdents;
            r = ((_2187_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out506;
            DCOMP._IOwnership _out507;
            (this).FromOwned(r, expectedOwnership, out _out506, out _out507);
            r = _out506;
            resultingOwnership = _out507;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapValues) {
          DAST._IExpression _2190_expr = _source109.dtor_expr;
          unmatched109 = false;
          {
            RAST._IExpr _2191_recursiveGen;
            DCOMP._IOwnership _2192___v194;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2193_recIdents;
            RAST._IExpr _out508;
            DCOMP._IOwnership _out509;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out510;
            (this).GenExpr(_2190_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out508, out _out509, out _out510);
            _2191_recursiveGen = _out508;
            _2192___v194 = _out509;
            _2193_recIdents = _out510;
            readIdents = _2193_recIdents;
            r = ((_2191_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out511;
            DCOMP._IOwnership _out512;
            (this).FromOwned(r, expectedOwnership, out _out511, out _out512);
            r = _out511;
            resultingOwnership = _out512;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapItems) {
          DAST._IExpression _2194_expr = _source109.dtor_expr;
          unmatched109 = false;
          {
            RAST._IExpr _2195_recursiveGen;
            DCOMP._IOwnership _2196___v195;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2197_recIdents;
            RAST._IExpr _out513;
            DCOMP._IOwnership _out514;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out515;
            (this).GenExpr(_2194_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out513, out _out514, out _out515);
            _2195_recursiveGen = _out513;
            _2196___v195 = _out514;
            _2197_recIdents = _out515;
            readIdents = _2197_recIdents;
            r = ((_2195_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("items"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out516;
            DCOMP._IOwnership _out517;
            (this).FromOwned(r, expectedOwnership, out _out516, out _out517);
            r = _out516;
            resultingOwnership = _out517;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SelectFn) {
          DAST._IExpression _2198_on = _source109.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2199_field = _source109.dtor_field;
          bool _2200_isDatatype = _source109.dtor_onDatatype;
          bool _2201_isStatic = _source109.dtor_isStatic;
          bool _2202_isConstant = _source109.dtor_isConstant;
          Dafny.ISequence<DAST._IType> _2203_arguments = _source109.dtor_arguments;
          unmatched109 = false;
          {
            RAST._IExpr _2204_onExpr;
            DCOMP._IOwnership _2205_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2206_recIdents;
            RAST._IExpr _out518;
            DCOMP._IOwnership _out519;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out520;
            (this).GenExpr(_2198_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out518, out _out519, out _out520);
            _2204_onExpr = _out518;
            _2205_onOwned = _out519;
            _2206_recIdents = _out520;
            Dafny.ISequence<Dafny.Rune> _2207_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2208_onString;
            _2208_onString = (_2204_onExpr)._ToString(DCOMP.__default.IND);
            if (_2201_isStatic) {
              DCOMP._IEnvironment _2209_lEnv;
              _2209_lEnv = env;
              Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>> _2210_args;
              _2210_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements();
              _2207_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|");
              BigInteger _hi46 = new BigInteger((_2203_arguments).Count);
              for (BigInteger _2211_i = BigInteger.Zero; _2211_i < _hi46; _2211_i++) {
                if ((_2211_i).Sign == 1) {
                  _2207_s = Dafny.Sequence<Dafny.Rune>.Concat(_2207_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                RAST._IType _2212_ty;
                RAST._IType _out521;
                _out521 = (this).GenType((_2203_arguments).Select(_2211_i), DCOMP.GenTypeContext.@default());
                _2212_ty = _out521;
                RAST._IType _2213_bTy;
                _2213_bTy = RAST.Type.create_Borrowed(_2212_ty);
                Dafny.ISequence<Dafny.Rune> _2214_name;
                _2214_name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), Std.Strings.__default.OfInt(_2211_i));
                _2209_lEnv = (_2209_lEnv).AddAssigned(_2214_name, _2213_bTy);
                _2210_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.Concat(_2210_args, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>.create(_2214_name, _2212_ty)));
                _2207_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2207_s, _2214_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_2213_bTy)._ToString(DCOMP.__default.IND));
              }
              _2207_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2207_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| ")), _2208_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeVar(_2199_field)), ((_2202_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("));
              BigInteger _hi47 = new BigInteger((_2210_args).Count);
              for (BigInteger _2215_i = BigInteger.Zero; _2215_i < _hi47; _2215_i++) {
                if ((_2215_i).Sign == 1) {
                  _2207_s = Dafny.Sequence<Dafny.Rune>.Concat(_2207_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType> _let_tmp_rhs68 = (_2210_args).Select(_2215_i);
                Dafny.ISequence<Dafny.Rune> _2216_name = _let_tmp_rhs68.dtor__0;
                RAST._IType _2217_ty = _let_tmp_rhs68.dtor__1;
                RAST._IExpr _2218_rIdent;
                DCOMP._IOwnership _2219___v196;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2220___v197;
                RAST._IExpr _out522;
                DCOMP._IOwnership _out523;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out524;
                (this).GenIdent(_2216_name, selfIdent, _2209_lEnv, (((_2217_ty).CanReadWithoutClone()) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed())), out _out522, out _out523, out _out524);
                _2218_rIdent = _out522;
                _2219___v196 = _out523;
                _2220___v197 = _out524;
                _2207_s = Dafny.Sequence<Dafny.Rune>.Concat(_2207_s, (_2218_rIdent)._ToString(DCOMP.__default.IND));
              }
              _2207_s = Dafny.Sequence<Dafny.Rune>.Concat(_2207_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            } else {
              _2207_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2207_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2207_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2208_onString), ((object.Equals(_2205_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2221_args;
              _2221_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2222_i;
              _2222_i = BigInteger.Zero;
              while ((_2222_i) < (new BigInteger((_2203_arguments).Count))) {
                if ((_2222_i).Sign == 1) {
                  _2221_args = Dafny.Sequence<Dafny.Rune>.Concat(_2221_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2221_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2221_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2222_i));
                _2222_i = (_2222_i) + (BigInteger.One);
              }
              _2207_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2207_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2221_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2207_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2207_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeVar(_2199_field)), ((_2202_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2221_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2207_s = Dafny.Sequence<Dafny.Rune>.Concat(_2207_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2207_s = Dafny.Sequence<Dafny.Rune>.Concat(_2207_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2223_typeShape;
            _2223_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2224_i;
            _2224_i = BigInteger.Zero;
            while ((_2224_i) < (new BigInteger((_2203_arguments).Count))) {
              if ((_2224_i).Sign == 1) {
                _2223_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2223_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2223_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2223_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2224_i = (_2224_i) + (BigInteger.One);
            }
            _2223_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2223_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2207_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2207_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2223_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2207_s);
            RAST._IExpr _out525;
            DCOMP._IOwnership _out526;
            (this).FromOwned(r, expectedOwnership, out _out525, out _out526);
            r = _out525;
            resultingOwnership = _out526;
            readIdents = _2206_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Select) {
          DAST._IExpression _2225_on = _source109.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2226_field = _source109.dtor_field;
          bool _2227_isConstant = _source109.dtor_isConstant;
          bool _2228_isDatatype = _source109.dtor_onDatatype;
          DAST._IType _2229_fieldType = _source109.dtor_fieldType;
          unmatched109 = false;
          {
            if (((_2225_on).is_Companion) || ((_2225_on).is_ExternCompanion)) {
              RAST._IExpr _2230_onExpr;
              DCOMP._IOwnership _2231_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2232_recIdents;
              RAST._IExpr _out527;
              DCOMP._IOwnership _out528;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
              (this).GenExpr(_2225_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out527, out _out528, out _out529);
              _2230_onExpr = _out527;
              _2231_onOwned = _out528;
              _2232_recIdents = _out529;
              r = ((_2230_onExpr).FSel(DCOMP.__default.escapeVar(_2226_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out530;
              DCOMP._IOwnership _out531;
              (this).FromOwned(r, expectedOwnership, out _out530, out _out531);
              r = _out530;
              resultingOwnership = _out531;
              readIdents = _2232_recIdents;
              return ;
            } else if (_2228_isDatatype) {
              RAST._IExpr _2233_onExpr;
              DCOMP._IOwnership _2234_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2235_recIdents;
              RAST._IExpr _out532;
              DCOMP._IOwnership _out533;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out534;
              (this).GenExpr(_2225_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out532, out _out533, out _out534);
              _2233_onExpr = _out532;
              _2234_onOwned = _out533;
              _2235_recIdents = _out534;
              r = ((_2233_onExpr).Sel(DCOMP.__default.escapeVar(_2226_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2236_typ;
              RAST._IType _out535;
              _out535 = (this).GenType(_2229_fieldType, DCOMP.GenTypeContext.@default());
              _2236_typ = _out535;
              RAST._IExpr _out536;
              DCOMP._IOwnership _out537;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out536, out _out537);
              r = _out536;
              resultingOwnership = _out537;
              readIdents = _2235_recIdents;
            } else {
              RAST._IExpr _2237_onExpr;
              DCOMP._IOwnership _2238_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2239_recIdents;
              RAST._IExpr _out538;
              DCOMP._IOwnership _out539;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out540;
              (this).GenExpr(_2225_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out538, out _out539, out _out540);
              _2237_onExpr = _out538;
              _2238_onOwned = _out539;
              _2239_recIdents = _out540;
              r = _2237_onExpr;
              if (!object.Equals(_2237_onExpr, RAST.__default.self)) {
                RAST._IExpr _source111 = _2237_onExpr;
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
              r = (r).Sel(DCOMP.__default.escapeVar(_2226_field));
              if (_2227_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out541;
              DCOMP._IOwnership _out542;
              (this).FromOwned(r, expectedOwnership, out _out541, out _out542);
              r = _out541;
              resultingOwnership = _out542;
              readIdents = _2239_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Index) {
          DAST._IExpression _2240_on = _source109.dtor_expr;
          DAST._ICollKind _2241_collKind = _source109.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2242_indices = _source109.dtor_indices;
          unmatched109 = false;
          {
            RAST._IExpr _2243_onExpr;
            DCOMP._IOwnership _2244_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2245_recIdents;
            RAST._IExpr _out543;
            DCOMP._IOwnership _out544;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out545;
            (this).GenExpr(_2240_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out543, out _out544, out _out545);
            _2243_onExpr = _out543;
            _2244_onOwned = _out544;
            _2245_recIdents = _out545;
            readIdents = _2245_recIdents;
            r = _2243_onExpr;
            bool _2246_hadArray;
            _2246_hadArray = false;
            if (object.Equals(_2241_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2246_hadArray = true;
              if ((new BigInteger((_2242_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi48 = new BigInteger((_2242_indices).Count);
            for (BigInteger _2247_i = BigInteger.Zero; _2247_i < _hi48; _2247_i++) {
              if (object.Equals(_2241_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2248_idx;
                DCOMP._IOwnership _2249_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2250_recIdentsIdx;
                RAST._IExpr _out546;
                DCOMP._IOwnership _out547;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out548;
                (this).GenExpr((_2242_indices).Select(_2247_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out546, out _out547, out _out548);
                _2248_idx = _out546;
                _2249_idxOwned = _out547;
                _2250_recIdentsIdx = _out548;
                _2248_idx = RAST.__default.IntoUsize(_2248_idx);
                r = RAST.Expr.create_SelectIndex(r, _2248_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2250_recIdentsIdx);
              } else {
                RAST._IExpr _2251_idx;
                DCOMP._IOwnership _2252_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2253_recIdentsIdx;
                RAST._IExpr _out549;
                DCOMP._IOwnership _out550;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out551;
                (this).GenExpr((_2242_indices).Select(_2247_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out549, out _out550, out _out551);
                _2251_idx = _out549;
                _2252_idxOwned = _out550;
                _2253_recIdentsIdx = _out551;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2251_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2253_recIdentsIdx);
              }
            }
            if (_2246_hadArray) {
              r = (r).Clone();
            }
            RAST._IExpr _out552;
            DCOMP._IOwnership _out553;
            (this).FromOwned(r, expectedOwnership, out _out552, out _out553);
            r = _out552;
            resultingOwnership = _out553;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_IndexRange) {
          DAST._IExpression _2254_on = _source109.dtor_expr;
          bool _2255_isArray = _source109.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2256_low = _source109.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2257_high = _source109.dtor_high;
          unmatched109 = false;
          {
            RAST._IExpr _2258_onExpr;
            DCOMP._IOwnership _2259_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2260_recIdents;
            RAST._IExpr _out554;
            DCOMP._IOwnership _out555;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out556;
            (this).GenExpr(_2254_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out554, out _out555, out _out556);
            _2258_onExpr = _out554;
            _2259_onOwned = _out555;
            _2260_recIdents = _out556;
            readIdents = _2260_recIdents;
            Dafny.ISequence<Dafny.Rune> _2261_methodName;
            _2261_methodName = (((_2256_low).is_Some) ? ((((_2257_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2257_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2262_arguments;
            _2262_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source112 = _2256_low;
            bool unmatched112 = true;
            if (unmatched112) {
              if (_source112.is_Some) {
                DAST._IExpression _2263_l = _source112.dtor_value;
                unmatched112 = false;
                {
                  RAST._IExpr _2264_lExpr;
                  DCOMP._IOwnership _2265___v200;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2266_recIdentsL;
                  RAST._IExpr _out557;
                  DCOMP._IOwnership _out558;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out559;
                  (this).GenExpr(_2263_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out557, out _out558, out _out559);
                  _2264_lExpr = _out557;
                  _2265___v200 = _out558;
                  _2266_recIdentsL = _out559;
                  _2262_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2262_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2264_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2266_recIdentsL);
                }
              }
            }
            if (unmatched112) {
              unmatched112 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source113 = _2257_high;
            bool unmatched113 = true;
            if (unmatched113) {
              if (_source113.is_Some) {
                DAST._IExpression _2267_h = _source113.dtor_value;
                unmatched113 = false;
                {
                  RAST._IExpr _2268_hExpr;
                  DCOMP._IOwnership _2269___v201;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2270_recIdentsH;
                  RAST._IExpr _out560;
                  DCOMP._IOwnership _out561;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out562;
                  (this).GenExpr(_2267_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out560, out _out561, out _out562);
                  _2268_hExpr = _out560;
                  _2269___v201 = _out561;
                  _2270_recIdentsH = _out562;
                  _2262_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2262_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2268_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2270_recIdentsH);
                }
              }
            }
            if (unmatched113) {
              unmatched113 = false;
            }
            r = _2258_onExpr;
            if (_2255_isArray) {
              if (!(_2261_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2261_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2261_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).FSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2261_methodName))).Apply(_2262_arguments);
            } else {
              if (!(_2261_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2261_methodName)).Apply(_2262_arguments);
              }
            }
            RAST._IExpr _out563;
            DCOMP._IOwnership _out564;
            (this).FromOwned(r, expectedOwnership, out _out563, out _out564);
            r = _out563;
            resultingOwnership = _out564;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_TupleSelect) {
          DAST._IExpression _2271_on = _source109.dtor_expr;
          BigInteger _2272_idx = _source109.dtor_index;
          DAST._IType _2273_fieldType = _source109.dtor_fieldType;
          unmatched109 = false;
          {
            RAST._IExpr _2274_onExpr;
            DCOMP._IOwnership _2275_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2276_recIdents;
            RAST._IExpr _out565;
            DCOMP._IOwnership _out566;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out567;
            (this).GenExpr(_2271_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out565, out _out566, out _out567);
            _2274_onExpr = _out565;
            _2275_onOwnership = _out566;
            _2276_recIdents = _out567;
            Dafny.ISequence<Dafny.Rune> _2277_selName;
            _2277_selName = Std.Strings.__default.OfNat(_2272_idx);
            DAST._IType _source114 = _2273_fieldType;
            bool unmatched114 = true;
            if (unmatched114) {
              if (_source114.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2278_tps = _source114.dtor_Tuple_a0;
                unmatched114 = false;
                if (((_2273_fieldType).is_Tuple) && ((new BigInteger((_2278_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2277_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2277_selName);
                }
              }
            }
            if (unmatched114) {
              unmatched114 = false;
            }
            r = ((_2274_onExpr).Sel(_2277_selName)).Clone();
            RAST._IExpr _out568;
            DCOMP._IOwnership _out569;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out568, out _out569);
            r = _out568;
            resultingOwnership = _out569;
            readIdents = _2276_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Call) {
          DAST._IExpression _2279_on = _source109.dtor_on;
          DAST._ICallName _2280_name = _source109.dtor_callName;
          Dafny.ISequence<DAST._IType> _2281_typeArgs = _source109.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2282_args = _source109.dtor_args;
          unmatched109 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2283_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2284_recIdents;
            Dafny.ISequence<RAST._IType> _2285_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2286_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out570;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out571;
            Dafny.ISequence<RAST._IType> _out572;
            Std.Wrappers._IOption<DAST._IResolvedType> _out573;
            (this).GenArgs(selfIdent, _2280_name, _2281_typeArgs, _2282_args, env, out _out570, out _out571, out _out572, out _out573);
            _2283_argExprs = _out570;
            _2284_recIdents = _out571;
            _2285_typeExprs = _out572;
            _2286_fullNameQualifier = _out573;
            readIdents = _2284_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source115 = _2286_fullNameQualifier;
            bool unmatched115 = true;
            if (unmatched115) {
              if (_source115.is_Some) {
                DAST._IResolvedType value11 = _source115.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2287_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2288_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2289_base = value11.dtor_kind;
                unmatched115 = false;
                RAST._IExpr _2290_fullPath;
                RAST._IExpr _out574;
                _out574 = DCOMP.COMP.GenPathExpr(_2287_path, true);
                _2290_fullPath = _out574;
                Dafny.ISequence<RAST._IType> _2291_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out575;
                _out575 = (this).GenTypeArgs(_2288_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2291_onTypeExprs = _out575;
                RAST._IExpr _2292_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2293_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2294_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2289_base).is_Trait) || ((_2289_base).is_Class)) {
                  RAST._IExpr _out576;
                  DCOMP._IOwnership _out577;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out578;
                  (this).GenExpr(_2279_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out576, out _out577, out _out578);
                  _2292_onExpr = _out576;
                  _2293_recOwnership = _out577;
                  _2294_recIdents = _out578;
                  _2292_onExpr = ((this).read__macro).Apply1(_2292_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2294_recIdents);
                } else {
                  RAST._IExpr _out579;
                  DCOMP._IOwnership _out580;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out581;
                  (this).GenExpr(_2279_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out579, out _out580, out _out581);
                  _2292_onExpr = _out579;
                  _2293_recOwnership = _out580;
                  _2294_recIdents = _out581;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2294_recIdents);
                }
                r = ((((_2290_fullPath).ApplyType(_2291_onTypeExprs)).FSel(DCOMP.__default.escapeName((_2280_name).dtor_name))).ApplyType(_2285_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2292_onExpr), _2283_argExprs));
                RAST._IExpr _out582;
                DCOMP._IOwnership _out583;
                (this).FromOwned(r, expectedOwnership, out _out582, out _out583);
                r = _out582;
                resultingOwnership = _out583;
              }
            }
            if (unmatched115) {
              unmatched115 = false;
              RAST._IExpr _2295_onExpr;
              DCOMP._IOwnership _2296___v207;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2297_recIdents;
              RAST._IExpr _out584;
              DCOMP._IOwnership _out585;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
              (this).GenExpr(_2279_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out584, out _out585, out _out586);
              _2295_onExpr = _out584;
              _2296___v207 = _out585;
              _2297_recIdents = _out586;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2297_recIdents);
              Dafny.ISequence<Dafny.Rune> _2298_renderedName;
              _2298_renderedName = (this).GetMethodName(_2279_on, _2280_name);
              DAST._IExpression _source116 = _2279_on;
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
                    _2295_onExpr = (_2295_onExpr).FSel(_2298_renderedName);
                  }
                }
              }
              if (unmatched116) {
                unmatched116 = false;
                {
                  if (!object.Equals(_2295_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source117 = _2280_name;
                    bool unmatched117 = true;
                    if (unmatched117) {
                      if (_source117.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source117.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2299_tpe = onType2.dtor_value;
                          unmatched117 = false;
                          RAST._IType _2300_typ;
                          RAST._IType _out587;
                          _out587 = (this).GenType(_2299_tpe, DCOMP.GenTypeContext.@default());
                          _2300_typ = _out587;
                          if ((_2300_typ).IsObjectOrPointer()) {
                            _2295_onExpr = ((this).read__macro).Apply1(_2295_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched117) {
                      unmatched117 = false;
                    }
                  }
                  _2295_onExpr = (_2295_onExpr).Sel(_2298_renderedName);
                }
              }
              r = ((_2295_onExpr).ApplyType(_2285_typeExprs)).Apply(_2283_argExprs);
              RAST._IExpr _out588;
              DCOMP._IOwnership _out589;
              (this).FromOwned(r, expectedOwnership, out _out588, out _out589);
              r = _out588;
              resultingOwnership = _out589;
              return ;
            }
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2301_paramsDafny = _source109.dtor_params;
          DAST._IType _2302_retType = _source109.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2303_body = _source109.dtor_body;
          unmatched109 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2304_params;
            Dafny.ISequence<RAST._IFormal> _out590;
            _out590 = (this).GenParams(_2301_paramsDafny, true);
            _2304_params = _out590;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2305_paramNames;
            _2305_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2306_paramTypesMap;
            _2306_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi49 = new BigInteger((_2304_params).Count);
            for (BigInteger _2307_i = BigInteger.Zero; _2307_i < _hi49; _2307_i++) {
              Dafny.ISequence<Dafny.Rune> _2308_name;
              _2308_name = ((_2304_params).Select(_2307_i)).dtor_name;
              _2305_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2305_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2308_name));
              _2306_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2306_paramTypesMap, _2308_name, ((_2304_params).Select(_2307_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2309_subEnv;
            _2309_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2305_paramNames, _2306_paramTypesMap));
            RAST._IExpr _2310_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2311_recIdents;
            DCOMP._IEnvironment _2312___v217;
            RAST._IExpr _out591;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out592;
            DCOMP._IEnvironment _out593;
            (this).GenStmts(_2303_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2309_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out591, out _out592, out _out593);
            _2310_recursiveGen = _out591;
            _2311_recIdents = _out592;
            _2312___v217 = _out593;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2311_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2311_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2313_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll8 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_9 in (_2313_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2314_name = (Dafny.ISequence<Dafny.Rune>)_compr_9;
                if ((_2313_paramNames).Contains(_2314_name)) {
                  _coll8.Add(_2314_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll8);
            }))())(_2305_paramNames));
            RAST._IExpr _2315_allReadCloned;
            _2315_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2311_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2316_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_4 in (_2311_recIdents).Elements) {
                _2316_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_4;
                if ((_2311_recIdents).Contains(_2316_next)) {
                  goto after__ASSIGN_SUCH_THAT_4;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 5198)");
            after__ASSIGN_SUCH_THAT_4: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2316_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2317_selfCloned;
                DCOMP._IOwnership _2318___v218;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2319___v219;
                RAST._IExpr _out594;
                DCOMP._IOwnership _out595;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out596;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out594, out _out595, out _out596);
                _2317_selfCloned = _out594;
                _2318___v218 = _out595;
                _2319___v219 = _out596;
                _2315_allReadCloned = (_2315_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2317_selfCloned)));
              } else if (!((_2305_paramNames).Contains(_2316_next))) {
                RAST._IExpr _2320_copy;
                _2320_copy = (RAST.Expr.create_Identifier(_2316_next)).Clone();
                _2315_allReadCloned = (_2315_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2316_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2320_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2316_next));
              }
              _2311_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2311_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2316_next));
            }
            RAST._IType _2321_retTypeGen;
            RAST._IType _out597;
            _out597 = (this).GenType(_2302_retType, DCOMP.GenTypeContext.InFn());
            _2321_retTypeGen = _out597;
            r = RAST.Expr.create_Block((_2315_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2304_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2321_retTypeGen), RAST.Expr.create_Block(_2310_recursiveGen)))));
            RAST._IExpr _out598;
            DCOMP._IOwnership _out599;
            (this).FromOwned(r, expectedOwnership, out _out598, out _out599);
            r = _out598;
            resultingOwnership = _out599;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2322_values = _source109.dtor_values;
          DAST._IType _2323_retType = _source109.dtor_retType;
          DAST._IExpression _2324_expr = _source109.dtor_expr;
          unmatched109 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2325_paramNames;
            _2325_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2326_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out600;
            _out600 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2327_value) => {
              return (_2327_value).dtor__0;
            })), _2322_values), false);
            _2326_paramFormals = _out600;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2328_paramTypes;
            _2328_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2329_paramNamesSet;
            _2329_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi50 = new BigInteger((_2322_values).Count);
            for (BigInteger _2330_i = BigInteger.Zero; _2330_i < _hi50; _2330_i++) {
              Dafny.ISequence<Dafny.Rune> _2331_name;
              _2331_name = (((_2322_values).Select(_2330_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2332_rName;
              _2332_rName = DCOMP.__default.escapeVar(_2331_name);
              _2325_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2325_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2332_rName));
              _2328_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2328_paramTypes, _2332_rName, ((_2326_paramFormals).Select(_2330_i)).dtor_tpe);
              _2329_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2329_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2332_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi51 = new BigInteger((_2322_values).Count);
            for (BigInteger _2333_i = BigInteger.Zero; _2333_i < _hi51; _2333_i++) {
              RAST._IType _2334_typeGen;
              RAST._IType _out601;
              _out601 = (this).GenType((((_2322_values).Select(_2333_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2334_typeGen = _out601;
              RAST._IExpr _2335_valueGen;
              DCOMP._IOwnership _2336___v220;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2337_recIdents;
              RAST._IExpr _out602;
              DCOMP._IOwnership _out603;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out604;
              (this).GenExpr(((_2322_values).Select(_2333_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out602, out _out603, out _out604);
              _2335_valueGen = _out602;
              _2336___v220 = _out603;
              _2337_recIdents = _out604;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar((((_2322_values).Select(_2333_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2334_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2335_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2337_recIdents);
            }
            DCOMP._IEnvironment _2338_newEnv;
            _2338_newEnv = DCOMP.Environment.create(_2325_paramNames, _2328_paramTypes);
            RAST._IExpr _2339_recGen;
            DCOMP._IOwnership _2340_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2341_recIdents;
            RAST._IExpr _out605;
            DCOMP._IOwnership _out606;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out607;
            (this).GenExpr(_2324_expr, selfIdent, _2338_newEnv, expectedOwnership, out _out605, out _out606, out _out607);
            _2339_recGen = _out605;
            _2340_recOwned = _out606;
            _2341_recIdents = _out607;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2341_recIdents, _2329_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2339_recGen));
            RAST._IExpr _out608;
            DCOMP._IOwnership _out609;
            (this).FromOwnership(r, _2340_recOwned, expectedOwnership, out _out608, out _out609);
            r = _out608;
            resultingOwnership = _out609;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2342_name = _source109.dtor_ident;
          DAST._IType _2343_tpe = _source109.dtor_typ;
          DAST._IExpression _2344_value = _source109.dtor_value;
          DAST._IExpression _2345_iifeBody = _source109.dtor_iifeBody;
          unmatched109 = false;
          {
            RAST._IExpr _2346_valueGen;
            DCOMP._IOwnership _2347___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2348_recIdents;
            RAST._IExpr _out610;
            DCOMP._IOwnership _out611;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out612;
            (this).GenExpr(_2344_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out610, out _out611, out _out612);
            _2346_valueGen = _out610;
            _2347___v221 = _out611;
            _2348_recIdents = _out612;
            readIdents = _2348_recIdents;
            RAST._IType _2349_valueTypeGen;
            RAST._IType _out613;
            _out613 = (this).GenType(_2343_tpe, DCOMP.GenTypeContext.InFn());
            _2349_valueTypeGen = _out613;
            RAST._IExpr _2350_bodyGen;
            DCOMP._IOwnership _2351___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2352_bodyIdents;
            RAST._IExpr _out614;
            DCOMP._IOwnership _out615;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out616;
            (this).GenExpr(_2345_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out614, out _out615, out _out616);
            _2350_bodyGen = _out614;
            _2351___v222 = _out615;
            _2352_bodyIdents = _out616;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2352_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_2342_name))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar(_2342_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2349_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2346_valueGen))).Then(_2350_bodyGen));
            RAST._IExpr _out617;
            DCOMP._IOwnership _out618;
            (this).FromOwned(r, expectedOwnership, out _out617, out _out618);
            r = _out617;
            resultingOwnership = _out618;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Apply) {
          DAST._IExpression _2353_func = _source109.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2354_args = _source109.dtor_args;
          unmatched109 = false;
          {
            RAST._IExpr _2355_funcExpr;
            DCOMP._IOwnership _2356___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2357_recIdents;
            RAST._IExpr _out619;
            DCOMP._IOwnership _out620;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out621;
            (this).GenExpr(_2353_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out619, out _out620, out _out621);
            _2355_funcExpr = _out619;
            _2356___v223 = _out620;
            _2357_recIdents = _out621;
            readIdents = _2357_recIdents;
            Dafny.ISequence<RAST._IExpr> _2358_rArgs;
            _2358_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi52 = new BigInteger((_2354_args).Count);
            for (BigInteger _2359_i = BigInteger.Zero; _2359_i < _hi52; _2359_i++) {
              RAST._IExpr _2360_argExpr;
              DCOMP._IOwnership _2361_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2362_argIdents;
              RAST._IExpr _out622;
              DCOMP._IOwnership _out623;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out624;
              (this).GenExpr((_2354_args).Select(_2359_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out622, out _out623, out _out624);
              _2360_argExpr = _out622;
              _2361_argOwned = _out623;
              _2362_argIdents = _out624;
              _2358_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2358_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2360_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2362_argIdents);
            }
            r = (_2355_funcExpr).Apply(_2358_rArgs);
            RAST._IExpr _out625;
            DCOMP._IOwnership _out626;
            (this).FromOwned(r, expectedOwnership, out _out625, out _out626);
            r = _out625;
            resultingOwnership = _out626;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_TypeTest) {
          DAST._IExpression _2363_on = _source109.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2364_dType = _source109.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2365_variant = _source109.dtor_variant;
          unmatched109 = false;
          {
            RAST._IExpr _2366_exprGen;
            DCOMP._IOwnership _2367___v224;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2368_recIdents;
            RAST._IExpr _out627;
            DCOMP._IOwnership _out628;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out629;
            (this).GenExpr(_2363_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out627, out _out628, out _out629);
            _2366_exprGen = _out627;
            _2367___v224 = _out628;
            _2368_recIdents = _out629;
            RAST._IType _2369_dTypePath;
            RAST._IType _out630;
            _out630 = DCOMP.COMP.GenPathType(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2364_dType, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2365_variant)));
            _2369_dTypePath = _out630;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2366_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_2369_dTypePath)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out631;
            DCOMP._IOwnership _out632;
            (this).FromOwned(r, expectedOwnership, out _out631, out _out632);
            r = _out631;
            resultingOwnership = _out632;
            readIdents = _2368_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_Is) {
          DAST._IExpression _2370_expr = _source109.dtor_expr;
          DAST._IType _2371_fromType = _source109.dtor_fromType;
          DAST._IType _2372_toType = _source109.dtor_toType;
          unmatched109 = false;
          {
            RAST._IExpr _2373_expr;
            DCOMP._IOwnership _2374_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2375_recIdents;
            RAST._IExpr _out633;
            DCOMP._IOwnership _out634;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out635;
            (this).GenExpr(_2370_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out633, out _out634, out _out635);
            _2373_expr = _out633;
            _2374_recOwned = _out634;
            _2375_recIdents = _out635;
            RAST._IType _2376_fromType;
            RAST._IType _out636;
            _out636 = (this).GenType(_2371_fromType, DCOMP.GenTypeContext.@default());
            _2376_fromType = _out636;
            RAST._IType _2377_toType;
            RAST._IType _out637;
            _out637 = (this).GenType(_2372_toType, DCOMP.GenTypeContext.@default());
            _2377_toType = _out637;
            if (((_2376_fromType).IsObject()) && ((_2377_toType).IsObject())) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is_instance_of_object"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((_2376_fromType).ObjectOrPointerUnderlying(), (_2377_toType).ObjectOrPointerUnderlying()))).Apply1(_2373_expr);
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Source and/or target types of type test is/are not Object"));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
            RAST._IExpr _out638;
            DCOMP._IOwnership _out639;
            (this).FromOwnership(r, _2374_recOwned, expectedOwnership, out _out638, out _out639);
            r = _out638;
            resultingOwnership = _out639;
            readIdents = _2375_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_BoolBoundedPool) {
          unmatched109 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out640;
            DCOMP._IOwnership _out641;
            (this).FromOwned(r, expectedOwnership, out _out640, out _out641);
            r = _out640;
            resultingOwnership = _out641;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SetBoundedPool) {
          DAST._IExpression _2378_of = _source109.dtor_of;
          unmatched109 = false;
          {
            RAST._IExpr _2379_exprGen;
            DCOMP._IOwnership _2380___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2381_recIdents;
            RAST._IExpr _out642;
            DCOMP._IOwnership _out643;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out644;
            (this).GenExpr(_2378_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out642, out _out643, out _out644);
            _2379_exprGen = _out642;
            _2380___v225 = _out643;
            _2381_recIdents = _out644;
            r = ((_2379_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out645;
            DCOMP._IOwnership _out646;
            (this).FromOwned(r, expectedOwnership, out _out645, out _out646);
            r = _out645;
            resultingOwnership = _out646;
            readIdents = _2381_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SeqBoundedPool) {
          DAST._IExpression _2382_of = _source109.dtor_of;
          bool _2383_includeDuplicates = _source109.dtor_includeDuplicates;
          unmatched109 = false;
          {
            RAST._IExpr _2384_exprGen;
            DCOMP._IOwnership _2385___v226;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2386_recIdents;
            RAST._IExpr _out647;
            DCOMP._IOwnership _out648;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out649;
            (this).GenExpr(_2382_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out647, out _out648, out _out649);
            _2384_exprGen = _out647;
            _2385___v226 = _out648;
            _2386_recIdents = _out649;
            r = ((_2384_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2383_includeDuplicates)) {
              r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).AsExpr()).Apply1(r);
            }
            RAST._IExpr _out650;
            DCOMP._IOwnership _out651;
            (this).FromOwned(r, expectedOwnership, out _out650, out _out651);
            r = _out650;
            resultingOwnership = _out651;
            readIdents = _2386_recIdents;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapBoundedPool) {
          DAST._IExpression _2387_of = _source109.dtor_of;
          unmatched109 = false;
          {
            RAST._IExpr _2388_exprGen;
            DCOMP._IOwnership _2389___v227;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2390_recIdents;
            RAST._IExpr _out652;
            DCOMP._IOwnership _out653;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out654;
            (this).GenExpr(_2387_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out652, out _out653, out _out654);
            _2388_exprGen = _out652;
            _2389___v227 = _out653;
            _2390_recIdents = _out654;
            r = ((((_2388_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2390_recIdents;
            RAST._IExpr _out655;
            DCOMP._IOwnership _out656;
            (this).FromOwned(r, expectedOwnership, out _out655, out _out656);
            r = _out655;
            resultingOwnership = _out656;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_IntRange) {
          DAST._IExpression _2391_lo = _source109.dtor_lo;
          DAST._IExpression _2392_hi = _source109.dtor_hi;
          bool _2393_up = _source109.dtor_up;
          unmatched109 = false;
          {
            RAST._IExpr _2394_lo;
            DCOMP._IOwnership _2395___v228;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2396_recIdentsLo;
            RAST._IExpr _out657;
            DCOMP._IOwnership _out658;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out659;
            (this).GenExpr(_2391_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out657, out _out658, out _out659);
            _2394_lo = _out657;
            _2395___v228 = _out658;
            _2396_recIdentsLo = _out659;
            RAST._IExpr _2397_hi;
            DCOMP._IOwnership _2398___v229;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2399_recIdentsHi;
            RAST._IExpr _out660;
            DCOMP._IOwnership _out661;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out662;
            (this).GenExpr(_2392_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out660, out _out661, out _out662);
            _2397_hi = _out660;
            _2398___v229 = _out661;
            _2399_recIdentsHi = _out662;
            if (_2393_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2394_lo, _2397_hi));
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2397_hi, _2394_lo));
            }
            RAST._IExpr _out663;
            DCOMP._IOwnership _out664;
            (this).FromOwned(r, expectedOwnership, out _out663, out _out664);
            r = _out663;
            resultingOwnership = _out664;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2396_recIdentsLo, _2399_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_UnboundedIntRange) {
          DAST._IExpression _2400_start = _source109.dtor_start;
          bool _2401_up = _source109.dtor_up;
          unmatched109 = false;
          {
            RAST._IExpr _2402_start;
            DCOMP._IOwnership _2403___v230;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2404_recIdentStart;
            RAST._IExpr _out665;
            DCOMP._IOwnership _out666;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out667;
            (this).GenExpr(_2400_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out665, out _out666, out _out667);
            _2402_start = _out665;
            _2403___v230 = _out666;
            _2404_recIdentStart = _out667;
            if (_2401_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).AsExpr()).Apply1(_2402_start);
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).AsExpr()).Apply1(_2402_start);
            }
            RAST._IExpr _out668;
            DCOMP._IOwnership _out669;
            (this).FromOwned(r, expectedOwnership, out _out668, out _out669);
            r = _out668;
            resultingOwnership = _out669;
            readIdents = _2404_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_MapBuilder) {
          DAST._IType _2405_keyType = _source109.dtor_keyType;
          DAST._IType _2406_valueType = _source109.dtor_valueType;
          unmatched109 = false;
          {
            RAST._IType _2407_kType;
            RAST._IType _out670;
            _out670 = (this).GenType(_2405_keyType, DCOMP.GenTypeContext.@default());
            _2407_kType = _out670;
            RAST._IType _2408_vType;
            RAST._IType _out671;
            _out671 = (this).GenType(_2406_valueType, DCOMP.GenTypeContext.@default());
            _2408_vType = _out671;
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2407_kType, _2408_vType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out672;
            DCOMP._IOwnership _out673;
            (this).FromOwned(r, expectedOwnership, out _out672, out _out673);
            r = _out672;
            resultingOwnership = _out673;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched109) {
        if (_source109.is_SetBuilder) {
          DAST._IType _2409_elemType = _source109.dtor_elemType;
          unmatched109 = false;
          {
            RAST._IType _2410_eType;
            RAST._IType _out674;
            _out674 = (this).GenType(_2409_elemType, DCOMP.GenTypeContext.@default());
            _2410_eType = _out674;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2410_eType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out675;
            DCOMP._IOwnership _out676;
            (this).FromOwned(r, expectedOwnership, out _out675, out _out676);
            r = _out675;
            resultingOwnership = _out676;
            return ;
          }
        }
      }
      if (unmatched109) {
        DAST._IType _2411_elemType = _source109.dtor_elemType;
        DAST._IExpression _2412_collection = _source109.dtor_collection;
        bool _2413_is__forall = _source109.dtor_is__forall;
        DAST._IExpression _2414_lambda = _source109.dtor_lambda;
        unmatched109 = false;
        {
          RAST._IType _2415_tpe;
          RAST._IType _out677;
          _out677 = (this).GenType(_2411_elemType, DCOMP.GenTypeContext.@default());
          _2415_tpe = _out677;
          RAST._IExpr _2416_collectionGen;
          DCOMP._IOwnership _2417___v231;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2418_recIdents;
          RAST._IExpr _out678;
          DCOMP._IOwnership _out679;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out680;
          (this).GenExpr(_2412_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out678, out _out679, out _out680);
          _2416_collectionGen = _out678;
          _2417___v231 = _out679;
          _2418_recIdents = _out680;
          Dafny.ISequence<DAST._IAttribute> _2419_extraAttributes;
          _2419_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2412_collection).is_IntRange) || ((_2412_collection).is_UnboundedIntRange)) || ((_2412_collection).is_SeqBoundedPool)) {
            _2419_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2414_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2420_formals;
            _2420_formals = (_2414_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2421_newFormals;
            _2421_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi53 = new BigInteger((_2420_formals).Count);
            for (BigInteger _2422_i = BigInteger.Zero; _2422_i < _hi53; _2422_i++) {
              var _pat_let_tv202 = _2419_extraAttributes;
              var _pat_let_tv203 = _2420_formals;
              _2421_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2421_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2420_formals).Select(_2422_i), _pat_let47_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let47_0, _2423_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv202, ((_pat_let_tv203).Select(_2422_i)).dtor_attributes), _pat_let48_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let48_0, _2424_dt__update_hattributes_h0 => DAST.Formal.create((_2423_dt__update__tmp_h0).dtor_name, (_2423_dt__update__tmp_h0).dtor_typ, _2424_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv204 = _2421_newFormals;
            DAST._IExpression _2425_newLambda;
            _2425_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2414_lambda, _pat_let49_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let49_0, _2426_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv204, _pat_let50_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let50_0, _2427_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2427_dt__update_hparams_h0, (_2426_dt__update__tmp_h1).dtor_retType, (_2426_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2428_lambdaGen;
            DCOMP._IOwnership _2429___v232;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2430_recLambdaIdents;
            RAST._IExpr _out681;
            DCOMP._IOwnership _out682;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out683;
            (this).GenExpr(_2425_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out681, out _out682, out _out683);
            _2428_lambdaGen = _out681;
            _2429___v232 = _out682;
            _2430_recLambdaIdents = _out683;
            Dafny.ISequence<Dafny.Rune> _2431_fn;
            _2431_fn = ((_2413_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2416_collectionGen).Sel(_2431_fn)).Apply1(((_2428_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2418_recIdents, _2430_recLambdaIdents);
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Quantifier without an inline lambda"));
            r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
          RAST._IExpr _out684;
          DCOMP._IOwnership _out685;
          (this).FromOwned(r, expectedOwnership, out _out684, out _out685);
          r = _out684;
          resultingOwnership = _out685;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> externalFiles)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      Dafny.ISequence<RAST._IModDecl> _2432_externUseDecls;
      _2432_externUseDecls = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi54 = new BigInteger((externalFiles).Count);
      for (BigInteger _2433_i = BigInteger.Zero; _2433_i < _hi54; _2433_i++) {
        Dafny.ISequence<Dafny.Rune> _2434_externalFile;
        _2434_externalFile = (externalFiles).Select(_2433_i);
        Dafny.ISequence<Dafny.Rune> _2435_externalMod;
        _2435_externalMod = _2434_externalFile;
        if (((new BigInteger((_2434_externalFile).Count)) > (new BigInteger(3))) && (((_2434_externalFile).Drop((new BigInteger((_2434_externalFile).Count)) - (new BigInteger(3)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".rs")))) {
          _2435_externalMod = (_2434_externalFile).Subsequence(BigInteger.Zero, (new BigInteger((_2434_externalFile).Count)) - (new BigInteger(3)));
        } else {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unrecognized external file "), _2434_externalFile), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". External file must be *.rs files")));
        }
        RAST._IMod _2436_externMod;
        _2436_externMod = RAST.Mod.create_ExternMod(_2435_externalMod);
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (_2436_externMod)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        _2432_externUseDecls = Dafny.Sequence<RAST._IModDecl>.Concat(_2432_externUseDecls, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), ((RAST.__default.crate).MSel(_2435_externalMod)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))));
      }
      if (!(_2432_externUseDecls).Equals(Dafny.Sequence<RAST._IModDecl>.FromElements())) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (RAST.Mod.create_Mod(DCOMP.COMP.DAFNY__EXTERN__MODULE, _2432_externUseDecls))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
      }
      BigInteger _hi55 = new BigInteger((p).Count);
      for (BigInteger _2437_i = BigInteger.Zero; _2437_i < _hi55; _2437_i++) {
        RAST._IMod _2438_m;
        RAST._IMod _out686;
        _out686 = (this).GenModule((p).Select(_2437_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2438_m = _out686;
        BigInteger _hi56 = new BigInteger((this.optimizations).Count);
        for (BigInteger _2439_j = BigInteger.Zero; _2439_j < _hi56; _2439_j++) {
          _2438_m = Dafny.Helpers.Id<Func<RAST._IMod, RAST._IMod>>((this.optimizations).Select(_2439_j))(_2438_m);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (_2438_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2440_i;
      _2440_i = BigInteger.Zero;
      while ((_2440_i) < (new BigInteger((fullName).Count))) {
        if ((_2440_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2440_i)));
        _2440_i = (_2440_i) + (BigInteger.One);
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