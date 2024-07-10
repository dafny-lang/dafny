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
      Dafny.ISequence<Dafny.Rune> _1286___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1286___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1286___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1286___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in137 = (i).Drop(new BigInteger(2));
        i = _in137;
        goto TAIL_CALL_START;
      } else {
        _1286___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1286___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in138 = (i).Drop(BigInteger.One);
        i = _in138;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1287___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1287___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1287___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1287___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in139 = (i).Drop(BigInteger.One);
        i = _in139;
        goto TAIL_CALL_START;
      } else {
        _1287___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1287___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1288_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1288_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeVar(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1289_r = (f);
      if ((DCOMP.__default.reserved__vars).Contains(_1289_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1289_r);
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
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _1290_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source65 = (rs).Select(BigInteger.Zero);
          {
            if (_source65.is_UserDefined) {
              DAST._IResolvedType _1291_resolvedType = _source65.dtor_resolved;
              return DCOMP.__default.TraitTypeContainingMethod(_1291_resolvedType, dafnyName);
            }
          }
          {
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source66 = _1290_res;
        {
          if (_source66.is_Some) {
            return _1290_res;
          }
        }
        {
          return DCOMP.__default.TraitTypeContainingMethodAux((rs).Drop(BigInteger.One), dafnyName);
        }
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethod(DAST._IResolvedType r, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DAST._IResolvedType _let_tmp_rhs53 = r;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1292_path = _let_tmp_rhs53.dtor_path;
      Dafny.ISequence<DAST._IType> _1293_typeArgs = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedTypeBase _1294_kind = _let_tmp_rhs53.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1295_attributes = _let_tmp_rhs53.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1296_properMethods = _let_tmp_rhs53.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1297_extendedTypes = _let_tmp_rhs53.dtor_extendedTypes;
      if ((_1296_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1297_extendedTypes, dafnyName);
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
      Dafny.ISequence<Dafny.Rune> _1298___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1298___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((s).Select(BigInteger.Zero)) == (new Dafny.Rune(' '))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1298___accumulator, s);
      } else {
        _1298___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1298___accumulator, ((((s).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")) : (Dafny.Sequence<Dafny.Rune>.FromElements((s).Select(BigInteger.Zero)))));
        Dafny.ISequence<Dafny.Rune> _in141 = (s).Drop(BigInteger.One);
        s = _in141;
        goto TAIL_CALL_START;
      }
    }
    public static DCOMP._IExternAttribute ExtractExtern(Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DCOMP._IExternAttribute res = DCOMP.ExternAttribute.Default();
      BigInteger _hi5 = new BigInteger((attributes).Count);
      for (BigInteger _1299_i = BigInteger.Zero; _1299_i < _hi5; _1299_i++) {
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _1300_attr;
        _1300_attr = DCOMP.__default.OptExtern((attributes).Select(_1299_i), dafnyName);
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _source67 = _1300_attr;
        {
          if (_source67.is_Some) {
            DCOMP._IExternAttribute _1301_n = _source67.dtor_value;
            res = _1301_n;
            return res;
            goto after_match1;
          }
        }
        {
        }
      after_match1: ;
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
      DCOMP._IEnvironment _1302_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1303_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll8 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_9 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1304_k = (Dafny.ISequence<Dafny.Rune>)_compr_9;
          if (((this).dtor_types).Contains(_1304_k)) {
            _coll8.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_1304_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_1304_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll8);
      }))();
      return DCOMP.Environment.create((_1302_dt__update__tmp_h0).dtor_names, _1303_dt__update_htypes_h0);
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
      BigInteger _1305_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1305_indexInEnv), ((this).dtor_names).Drop((_1305_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      return Std.Collections.Seq.__default.Map<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>(((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1306_i) => {
        return DCOMP.__default.escapeName((_1306_i));
      })), containingPath);
    }
    public DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> s = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Default();
      _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs54 = DafnyCompilerRustUtils.__default.DafnyNameToContainingPathAndName((mod).dtor_name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1307_innerPath = _let_tmp_rhs54.dtor__0;
      Dafny.ISequence<Dafny.Rune> _1308_innerName = _let_tmp_rhs54.dtor__1;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1309_containingPath;
      _1309_containingPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, _1307_innerPath);
      Dafny.ISequence<Dafny.Rune> _1310_modName;
      _1310_modName = DCOMP.__default.escapeName(_1308_innerName);
      if (((mod).dtor_body).is_None) {
        s = DafnyCompilerRustUtils.GatheringModule.Wrap(DCOMP.COMP.ContainingPathToRust(_1309_containingPath), RAST.Mod.create_ExternMod(_1310_modName));
      } else {
        DCOMP._IExternAttribute _1311_optExtern;
        _1311_optExtern = DCOMP.__default.ExtractExternMod(mod);
        Dafny.ISequence<RAST._IModDecl> _1312_body;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _1313_allmodules;
        Dafny.ISequence<RAST._IModDecl> _out15;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out16;
        (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1309_containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1308_innerName)), out _out15, out _out16);
        _1312_body = _out15;
        _1313_allmodules = _out16;
        if ((_1311_optExtern).is_SimpleExtern) {
          if ((mod).dtor_requiresExterns) {
            _1312_body = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (((RAST.__default.crate).MSel(DCOMP.COMP.DAFNY__EXTERN__MODULE)).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1311_optExtern).dtor_overrideName))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))), _1312_body);
          }
        } else if ((_1311_optExtern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Externs on modules can only have 1 string argument"));
        } else if ((_1311_optExtern).is_UnsupportedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some((_1311_optExtern).dtor_reason);
        }
        s = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(DafnyCompilerRustUtils.GatheringModule.Wrap(DCOMP.COMP.ContainingPathToRust(_1309_containingPath), RAST.Mod.create_Mod(_1310_modName, _1312_body)), _1313_allmodules);
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
      for (BigInteger _1314_i = BigInteger.Zero; _1314_i < _hi6; _1314_i++) {
        Dafny.ISequence<RAST._IModDecl> _1315_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source68 = (body).Select(_1314_i);
        {
          if (_source68.is_Module) {
            DAST._IModule _1316_m = _source68.dtor_Module_a0;
            DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _1317_mm;
            DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out17;
            _out17 = (this).GenModule(_1316_m, containingPath);
            _1317_mm = _out17;
            allmodules = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(allmodules, _1317_mm);
            _1315_generated = Dafny.Sequence<RAST._IModDecl>.FromElements();
            goto after_match2;
          }
        }
        {
          if (_source68.is_Class) {
            DAST._IClass _1318_c = _source68.dtor_Class_a0;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenClass(_1318_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1318_c).dtor_name)));
            _1315_generated = _out18;
            goto after_match2;
          }
        }
        {
          if (_source68.is_Trait) {
            DAST._ITrait _1319_t = _source68.dtor_Trait_a0;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenTrait(_1319_t, containingPath);
            _1315_generated = _out19;
            goto after_match2;
          }
        }
        {
          if (_source68.is_Newtype) {
            DAST._INewtype _1320_n = _source68.dtor_Newtype_a0;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenNewtype(_1320_n);
            _1315_generated = _out20;
            goto after_match2;
          }
        }
        {
          if (_source68.is_SynonymType) {
            DAST._ISynonymType _1321_s = _source68.dtor_SynonymType_a0;
            Dafny.ISequence<RAST._IModDecl> _out21;
            _out21 = (this).GenSynonymType(_1321_s);
            _1315_generated = _out21;
            goto after_match2;
          }
        }
        {
          DAST._IDatatype _1322_d = _source68.dtor_Datatype_a0;
          Dafny.ISequence<RAST._IModDecl> _out22;
          _out22 = (this).GenDatatype(_1322_d);
          _1315_generated = _out22;
        }
      after_match2: ;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1315_generated);
      }
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1323_genTpConstraint;
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) {
        _1323_genTpConstraint = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq);
      } else {
        _1323_genTpConstraint = Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType);
      }
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1323_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1323_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1323_genTpConstraint);
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
        for (BigInteger _1324_tpI = BigInteger.Zero; _1324_tpI < _hi7; _1324_tpI++) {
          DAST._ITypeArgDecl _1325_tp;
          _1325_tp = (@params).Select(_1324_tpI);
          DAST._IType _1326_typeArg;
          RAST._ITypeParamDecl _1327_typeParam;
          DAST._IType _out23;
          RAST._ITypeParamDecl _out24;
          (this).GenTypeParam(_1325_tp, out _out23, out _out24);
          _1326_typeArg = _out23;
          _1327_typeParam = _out24;
          RAST._IType _1328_rType;
          RAST._IType _out25;
          _out25 = (this).GenType(_1326_typeArg, DCOMP.GenTypeContext.@default());
          _1328_rType = _out25;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1326_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1328_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1327_typeParam));
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
      return (typ).Fold<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>(types, ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>, RAST._IType, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)((_1329_types, _1330_currentType) => {
        return (((_1330_currentType).is_TIdentifier) ? (Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1329_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements((_1330_currentType).dtor_name))) : (_1329_types));
      })));
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1331_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1332_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1333_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1334_whereConstraints;
      Dafny.ISequence<DAST._IType> _out26;
      Dafny.ISequence<RAST._IType> _out27;
      Dafny.ISequence<RAST._ITypeParamDecl> _out28;
      Dafny.ISequence<Dafny.Rune> _out29;
      (this).GenTypeParameters((c).dtor_typeParams, out _out26, out _out27, out _out28, out _out29);
      _1331_typeParamsSeq = _out26;
      _1332_rTypeParams = _out27;
      _1333_rTypeParamsDecls = _out28;
      _1334_whereConstraints = _out29;
      Dafny.ISequence<Dafny.Rune> _1335_constrainedTypeParams;
      _1335_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1333_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1336_fields;
      _1336_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1337_fieldInits;
      _1337_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1338_usedTypeParams;
      _1338_usedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi8 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1339_fieldI = BigInteger.Zero; _1339_fieldI < _hi8; _1339_fieldI++) {
        DAST._IField _1340_field;
        _1340_field = ((c).dtor_fields).Select(_1339_fieldI);
        RAST._IType _1341_fieldType;
        RAST._IType _out30;
        _out30 = (this).GenType(((_1340_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1341_fieldType = _out30;
        _1338_usedTypeParams = (this).GatherTypeParamNames(_1338_usedTypeParams, _1341_fieldType);
        Dafny.ISequence<Dafny.Rune> _1342_fieldRustName;
        _1342_fieldRustName = DCOMP.__default.escapeVar(((_1340_field).dtor_formal).dtor_name);
        _1336_fields = Dafny.Sequence<RAST._IField>.Concat(_1336_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1342_fieldRustName, _1341_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source69 = (_1340_field).dtor_defaultValue;
        {
          if (_source69.is_Some) {
            DAST._IExpression _1343_e = _source69.dtor_value;
            {
              RAST._IExpr _1344_expr;
              DCOMP._IOwnership _1345___v51;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1346___v52;
              RAST._IExpr _out31;
              DCOMP._IOwnership _out32;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out33;
              (this).GenExpr(_1343_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out31, out _out32, out _out33);
              _1344_expr = _out31;
              _1345___v51 = _out32;
              _1346___v52 = _out33;
              _1337_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1337_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1342_fieldRustName, _1344_expr)));
            }
            goto after_match3;
          }
        }
        {
          {
            RAST._IExpr _1347_default;
            _1347_default = RAST.__default.std__Default__default;
            if ((_1341_fieldType).IsObjectOrPointer()) {
              _1347_default = (_1341_fieldType).ToNullExpr();
            }
            _1337_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1337_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1342_fieldRustName, _1347_default)));
          }
        }
      after_match3: ;
      }
      BigInteger _hi9 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1348_typeParamI = BigInteger.Zero; _1348_typeParamI < _hi9; _1348_typeParamI++) {
        DAST._IType _1349_typeArg;
        RAST._ITypeParamDecl _1350_typeParam;
        DAST._IType _out34;
        RAST._ITypeParamDecl _out35;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1348_typeParamI), out _out34, out _out35);
        _1349_typeArg = _out34;
        _1350_typeParam = _out35;
        RAST._IType _1351_rTypeArg;
        RAST._IType _out36;
        _out36 = (this).GenType(_1349_typeArg, DCOMP.GenTypeContext.@default());
        _1351_rTypeArg = _out36;
        if ((_1338_usedTypeParams).Contains((_1350_typeParam).dtor_name)) {
          goto continue_0;
        }
        _1336_fields = Dafny.Sequence<RAST._IField>.Concat(_1336_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1348_typeParamI)), RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1351_rTypeArg))))));
        _1337_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1337_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1348_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      continue_0: ;
      }
    after_0: ;
      DCOMP._IExternAttribute _1352_extern;
      _1352_extern = DCOMP.__default.ExtractExtern((c).dtor_attributes, (c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _1353_className = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((_1352_extern).is_SimpleExtern) {
        _1353_className = (_1352_extern).dtor_overrideName;
      } else {
        _1353_className = DCOMP.__default.escapeName((c).dtor_name);
        if ((_1352_extern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multi-argument externs not supported for classes yet"));
        }
      }
      RAST._IStruct _1354_struct;
      _1354_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1353_className, _1333_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1336_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_1352_extern).is_NoExtern) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1354_struct)));
      }
      Dafny.ISequence<RAST._IImplMember> _1355_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1356_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out37;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out38;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1331_typeParamsSeq, out _out37, out _out38);
      _1355_implBody = _out37;
      _1356_traitBodies = _out38;
      if (((_1352_extern).is_NoExtern) && (!(_1353_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default")))) {
        _1355_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.__default.SelfOwned)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel((this).allocate)).AsExpr()).ApplyType1(RAST.__default.SelfOwned)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1355_implBody);
      }
      RAST._IType _1357_selfTypeForImpl = RAST.Type.Default();
      if (((_1352_extern).is_NoExtern) || ((_1352_extern).is_UnsupportedExtern)) {
        _1357_selfTypeForImpl = RAST.Type.create_TIdentifier(_1353_className);
      } else if ((_1352_extern).is_AdvancedExtern) {
        _1357_selfTypeForImpl = (((RAST.__default.crate).MSel((_1352_extern).dtor_enclosingModule)).MSel((_1352_extern).dtor_overrideName)).AsType();
      } else if ((_1352_extern).is_SimpleExtern) {
        _1357_selfTypeForImpl = RAST.Type.create_TIdentifier((_1352_extern).dtor_overrideName);
      }
      if ((new BigInteger((_1355_implBody).Count)).Sign == 1) {
        RAST._IImpl _1358_i;
        _1358_i = RAST.Impl.create_Impl(_1333_rTypeParamsDecls, RAST.Type.create_TypeApp(_1357_selfTypeForImpl, _1332_rTypeParams), _1334_whereConstraints, _1355_implBody);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1358_i)));
      }
      RAST._IType _1359_genSelfPath;
      RAST._IType _out39;
      _out39 = DCOMP.COMP.GenPathType(path);
      _1359_genSelfPath = _out39;
      if (!(_1353_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1333_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(RAST.__default.AnyTrait))), RAST.Type.create_TypeApp(_1359_genSelfPath, _1332_rTypeParams), _1334_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(RAST.__default.AnyTrait)))))))));
      }
      Dafny.ISequence<DAST._IType> _1360_superClasses;
      if ((_1353_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        _1360_superClasses = Dafny.Sequence<DAST._IType>.FromElements();
      } else {
        _1360_superClasses = (c).dtor_superClasses;
      }
      BigInteger _hi10 = new BigInteger((_1360_superClasses).Count);
      for (BigInteger _1361_i = BigInteger.Zero; _1361_i < _hi10; _1361_i++) {
        DAST._IType _1362_superClass;
        _1362_superClass = (_1360_superClasses).Select(_1361_i);
        DAST._IType _source70 = _1362_superClass;
        {
          if (_source70.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source70.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1363_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1364_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1365_properMethods = resolved0.dtor_properMethods;
              {
                RAST._IType _1366_pathStr;
                RAST._IType _out40;
                _out40 = DCOMP.COMP.GenPathType(_1363_traitPath);
                _1366_pathStr = _out40;
                Dafny.ISequence<RAST._IType> _1367_typeArgs;
                Dafny.ISequence<RAST._IType> _out41;
                _out41 = (this).GenTypeArgs(_1364_typeArgs, DCOMP.GenTypeContext.@default());
                _1367_typeArgs = _out41;
                Dafny.ISequence<RAST._IImplMember> _1368_body;
                _1368_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1356_traitBodies).Contains(_1363_traitPath)) {
                  _1368_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1356_traitBodies,_1363_traitPath);
                }
                RAST._IType _1369_traitType;
                _1369_traitType = RAST.Type.create_TypeApp(_1366_pathStr, _1367_typeArgs);
                if (!((_1352_extern).is_NoExtern)) {
                  if (((new BigInteger((_1368_body).Count)).Sign == 0) && ((new BigInteger((_1365_properMethods).Count)).Sign != 0)) {
                    goto continue_1;
                  }
                  if ((new BigInteger((_1368_body).Count)) != (new BigInteger((_1365_properMethods).Count))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: In the class "), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(path, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1370_s) => {
  return ((_1370_s));
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", some proper methods of ")), (_1369_traitType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" are marked {:extern} and some are not.")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" For the Rust compiler, please make all methods (")), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_1365_properMethods, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1371_s) => {
  return (_1371_s);
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")  bodiless and mark as {:extern} and implement them in a Rust file, ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("or mark none of them as {:extern} and implement them in Dafny. ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.")));
                  }
                }
                RAST._IModDecl _1372_x;
                _1372_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1333_rTypeParamsDecls, _1369_traitType, RAST.Type.create_TypeApp(_1359_genSelfPath, _1332_rTypeParams), _1334_whereConstraints, _1368_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1372_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1333_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1369_traitType))), RAST.Type.create_TypeApp(_1359_genSelfPath, _1332_rTypeParams), _1334_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1369_traitType)))))))));
              }
              goto after_match4;
            }
          }
        }
        {
        }
      after_match4: ;
      continue_1: ;
      }
    after_1: ;
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1373_typeParamsSeq;
      _1373_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1374_typeParamDecls;
      _1374_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1375_typeParams;
      _1375_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi11 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1376_tpI = BigInteger.Zero; _1376_tpI < _hi11; _1376_tpI++) {
          DAST._ITypeArgDecl _1377_tp;
          _1377_tp = ((t).dtor_typeParams).Select(_1376_tpI);
          DAST._IType _1378_typeArg;
          RAST._ITypeParamDecl _1379_typeParamDecl;
          DAST._IType _out42;
          RAST._ITypeParamDecl _out43;
          (this).GenTypeParam(_1377_tp, out _out42, out _out43);
          _1378_typeArg = _out42;
          _1379_typeParamDecl = _out43;
          _1373_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1373_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1378_typeArg));
          _1374_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1374_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1379_typeParamDecl));
          RAST._IType _1380_typeParam;
          RAST._IType _out44;
          _out44 = (this).GenType(_1378_typeArg, DCOMP.GenTypeContext.@default());
          _1380_typeParam = _out44;
          _1375_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1375_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1380_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1381_fullPath;
      _1381_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1382_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1383___v56;
      Dafny.ISequence<RAST._IImplMember> _out45;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out46;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1381_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1373_typeParamsSeq, out _out45, out _out46);
      _1382_implBody = _out45;
      _1383___v56 = _out46;
      Dafny.ISequence<RAST._IType> _1384_parents;
      _1384_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi12 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1385_i = BigInteger.Zero; _1385_i < _hi12; _1385_i++) {
        RAST._IType _1386_tpe;
        RAST._IType _out47;
        _out47 = (this).GenType(((t).dtor_parents).Select(_1385_i), DCOMP.GenTypeContext.ForTraitParents());
        _1386_tpe = _out47;
        _1384_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1384_parents, Dafny.Sequence<RAST._IType>.FromElements(_1386_tpe)), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply1(RAST.Type.create_DynType(_1386_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1374_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1375_typeParams), _1384_parents, _1382_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1387_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1388_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1389_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1390_whereConstraints;
      Dafny.ISequence<DAST._IType> _out48;
      Dafny.ISequence<RAST._IType> _out49;
      Dafny.ISequence<RAST._ITypeParamDecl> _out50;
      Dafny.ISequence<Dafny.Rune> _out51;
      (this).GenTypeParameters((c).dtor_typeParams, out _out48, out _out49, out _out50, out _out51);
      _1387_typeParamsSeq = _out48;
      _1388_rTypeParams = _out49;
      _1389_rTypeParamsDecls = _out50;
      _1390_whereConstraints = _out51;
      Dafny.ISequence<Dafny.Rune> _1391_constrainedTypeParams;
      _1391_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1389_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1392_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source71 = DCOMP.COMP.NewtypeRangeToRustType((c).dtor_range);
      {
        if (_source71.is_Some) {
          RAST._IType _1393_v = _source71.dtor_value;
          _1392_underlyingType = _1393_v;
          goto after_match5;
        }
      }
      {
        RAST._IType _out52;
        _out52 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1392_underlyingType = _out52;
      }
    after_match5: ;
      DAST._IType _1394_resultingType;
      _1394_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1395_newtypeName;
      _1395_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1395_newtypeName, _1389_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1392_underlyingType))))));
      RAST._IExpr _1396_fnBody;
      _1396_fnBody = RAST.Expr.create_Identifier(_1395_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source72 = (c).dtor_witnessExpr;
      {
        if (_source72.is_Some) {
          DAST._IExpression _1397_e = _source72.dtor_value;
          {
            DAST._IExpression _1398_e;
            if (object.Equals((c).dtor_base, _1394_resultingType)) {
              _1398_e = _1397_e;
            } else {
              _1398_e = DAST.Expression.create_Convert(_1397_e, (c).dtor_base, _1394_resultingType);
            }
            RAST._IExpr _1399_eStr;
            DCOMP._IOwnership _1400___v57;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1401___v58;
            RAST._IExpr _out53;
            DCOMP._IOwnership _out54;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out55;
            (this).GenExpr(_1398_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out53, out _out54, out _out55);
            _1399_eStr = _out53;
            _1400___v57 = _out54;
            _1401___v58 = _out55;
            _1396_fnBody = (_1396_fnBody).Apply1(_1399_eStr);
          }
          goto after_match6;
        }
      }
      {
        {
          _1396_fnBody = (_1396_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
    after_match6: ;
      RAST._IImplMember _1402_body;
      _1402_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1396_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source73 = (c).dtor_constraint;
      {
        if (_source73.is_None) {
          goto after_match7;
        }
      }
      {
        DAST._INewtypeConstraint value8 = _source73.dtor_value;
        DAST._IFormal _1403_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1404_constraintStmts = value8.dtor_constraintStmts;
        RAST._IExpr _1405_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1406___v59;
        DCOMP._IEnvironment _1407_newEnv;
        RAST._IExpr _out56;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out57;
        DCOMP._IEnvironment _out58;
        (this).GenStmts(_1404_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out56, out _out57, out _out58);
        _1405_rStmts = _out56;
        _1406___v59 = _out57;
        _1407_newEnv = _out58;
        Dafny.ISequence<RAST._IFormal> _1408_rFormals;
        Dafny.ISequence<RAST._IFormal> _out59;
        _out59 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1403_formal), false);
        _1408_rFormals = _out59;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1389_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1395_newtypeName), _1388_rTypeParams), _1390_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1408_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1405_rStmts))))))));
      }
    after_match7: ;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1389_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1395_newtypeName), _1388_rTypeParams), _1390_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1402_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1389_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1395_newtypeName), _1388_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1389_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1395_newtypeName), _1388_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1392_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(((RAST.Path.create_Self()).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))).AsType())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1409_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1410_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1411_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1412_whereConstraints;
      Dafny.ISequence<DAST._IType> _out60;
      Dafny.ISequence<RAST._IType> _out61;
      Dafny.ISequence<RAST._ITypeParamDecl> _out62;
      Dafny.ISequence<Dafny.Rune> _out63;
      (this).GenTypeParameters((c).dtor_typeParams, out _out60, out _out61, out _out62, out _out63);
      _1409_typeParamsSeq = _out60;
      _1410_rTypeParams = _out61;
      _1411_rTypeParamsDecls = _out62;
      _1412_whereConstraints = _out63;
      Dafny.ISequence<Dafny.Rune> _1413_synonymTypeName;
      _1413_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1414_resultingType;
      RAST._IType _out64;
      _out64 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1414_resultingType = _out64;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1413_synonymTypeName, _1411_rTypeParamsDecls, _1414_resultingType)));
      Dafny.ISequence<RAST._ITypeParamDecl> _1415_defaultConstrainedTypeParams;
      _1415_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1411_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Std.Wrappers._IOption<DAST._IExpression> _source74 = (c).dtor_witnessExpr;
      {
        if (_source74.is_Some) {
          DAST._IExpression _1416_e = _source74.dtor_value;
          {
            RAST._IExpr _1417_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1418___v60;
            DCOMP._IEnvironment _1419_newEnv;
            RAST._IExpr _out65;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out66;
            DCOMP._IEnvironment _out67;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out65, out _out66, out _out67);
            _1417_rStmts = _out65;
            _1418___v60 = _out66;
            _1419_newEnv = _out67;
            RAST._IExpr _1420_rExpr;
            DCOMP._IOwnership _1421___v61;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1422___v62;
            RAST._IExpr _out68;
            DCOMP._IOwnership _out69;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out70;
            (this).GenExpr(_1416_e, DCOMP.SelfInfo.create_NoSelf(), _1419_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out68, out _out69, out _out70);
            _1420_rExpr = _out68;
            _1421___v61 = _out69;
            _1422___v62 = _out70;
            Dafny.ISequence<Dafny.Rune> _1423_constantName;
            _1423_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1423_constantName, _1415_defaultConstrainedTypeParams, Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1414_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1417_rStmts).Then(_1420_rExpr)))))));
          }
          goto after_match8;
        }
      }
      {
      }
    after_match8: ;
      return s;
    }
    public bool TypeIsEq(DAST._IType t) {
      DAST._IType _source75 = t;
      {
        if (_source75.is_UserDefined) {
          return true;
        }
      }
      {
        if (_source75.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1424_ts = _source75.dtor_Tuple_a0;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1425_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1425_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1426_t = (DAST._IType)_forall_var_5;
            return !((_1425_ts).Contains(_1426_t)) || ((this).TypeIsEq(_1426_t));
          }))))(_1424_ts);
        }
      }
      {
        if (_source75.is_Array) {
          DAST._IType _1427_t = _source75.dtor_element;
          return (this).TypeIsEq(_1427_t);
        }
      }
      {
        if (_source75.is_Seq) {
          DAST._IType _1428_t = _source75.dtor_element;
          return (this).TypeIsEq(_1428_t);
        }
      }
      {
        if (_source75.is_Set) {
          DAST._IType _1429_t = _source75.dtor_element;
          return (this).TypeIsEq(_1429_t);
        }
      }
      {
        if (_source75.is_Multiset) {
          DAST._IType _1430_t = _source75.dtor_element;
          return (this).TypeIsEq(_1430_t);
        }
      }
      {
        if (_source75.is_Map) {
          DAST._IType _1431_k = _source75.dtor_key;
          DAST._IType _1432_v = _source75.dtor_value;
          return ((this).TypeIsEq(_1431_k)) && ((this).TypeIsEq(_1432_v));
        }
      }
      {
        if (_source75.is_SetBuilder) {
          DAST._IType _1433_t = _source75.dtor_element;
          return (this).TypeIsEq(_1433_t);
        }
      }
      {
        if (_source75.is_MapBuilder) {
          DAST._IType _1434_k = _source75.dtor_key;
          DAST._IType _1435_v = _source75.dtor_value;
          return ((this).TypeIsEq(_1434_k)) && ((this).TypeIsEq(_1435_v));
        }
      }
      {
        if (_source75.is_Arrow) {
          return false;
        }
      }
      {
        if (_source75.is_Primitive) {
          return true;
        }
      }
      {
        if (_source75.is_Passthrough) {
          return true;
        }
      }
      {
        if (_source75.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _1436_i = _source75.dtor_TypeArg_a0;
          return true;
        }
      }
      {
        return true;
      }
    }
    public bool DatatypeIsEq(DAST._IDatatype c) {
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1437_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1437_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1438_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1438_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1439_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1437_c).dtor_ctors).Contains(_1438_ctor)) && (((_1438_ctor).dtor_args).Contains(_1439_arg))) || ((this).TypeIsEq(((_1439_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1440_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1441_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1442_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1443_whereConstraints;
      Dafny.ISequence<DAST._IType> _out71;
      Dafny.ISequence<RAST._IType> _out72;
      Dafny.ISequence<RAST._ITypeParamDecl> _out73;
      Dafny.ISequence<Dafny.Rune> _out74;
      (this).GenTypeParameters((c).dtor_typeParams, out _out71, out _out72, out _out73, out _out74);
      _1440_typeParamsSeq = _out71;
      _1441_rTypeParams = _out72;
      _1442_rTypeParamsDecls = _out73;
      _1443_whereConstraints = _out74;
      Dafny.ISequence<Dafny.Rune> _1444_datatypeName;
      _1444_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1445_ctors;
      _1445_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _1446_variances;
      _1446_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_1447_typeParamDecl) => {
        return (_1447_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1448_usedTypeParams;
      _1448_usedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
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
          _1448_usedTypeParams = (this).GatherTypeParamNames(_1448_usedTypeParams, _1455_formalType);
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
        _1445_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1445_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1450_ctor).dtor_name), _1457_namedFields)));
      }
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1458_unusedTypeParams;
      _1458_unusedTypeParams = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Helpers.Id<Func<Dafny.ISequence<RAST._ITypeParamDecl>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_1459_rTypeParamsDecls) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
        var _coll9 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
        foreach (RAST._ITypeParamDecl _compr_10 in (_1459_rTypeParamsDecls).CloneAsArray()) {
          RAST._ITypeParamDecl _1460_tp = (RAST._ITypeParamDecl)_compr_10;
          if ((_1459_rTypeParamsDecls).Contains(_1460_tp)) {
            _coll9.Add((_1460_tp).dtor_name);
          }
        }
        return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll9);
      }))())(_1442_rTypeParamsDecls), _1448_usedTypeParams);
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1461_selfPath;
      _1461_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1462_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1463_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out76;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out77;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1461_selfPath, _1440_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1446_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1440_typeParamsSeq, out _out76, out _out77);
      _1462_implBodyRaw = _out76;
      _1463_traitBodies = _out77;
      Dafny.ISequence<RAST._IImplMember> _1464_implBody;
      _1464_implBody = _1462_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1465_emittedFields;
      _1465_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi15 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1466_i = BigInteger.Zero; _1466_i < _hi15; _1466_i++) {
        DAST._IDatatypeCtor _1467_ctor;
        _1467_ctor = ((c).dtor_ctors).Select(_1466_i);
        BigInteger _hi16 = new BigInteger(((_1467_ctor).dtor_args).Count);
        for (BigInteger _1468_j = BigInteger.Zero; _1468_j < _hi16; _1468_j++) {
          DAST._IDatatypeDtor _1469_dtor;
          _1469_dtor = ((_1467_ctor).dtor_args).Select(_1468_j);
          Dafny.ISequence<Dafny.Rune> _1470_callName;
          _1470_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1469_dtor).dtor_callName, DCOMP.__default.escapeVar(((_1469_dtor).dtor_formal).dtor_name));
          if (!((_1465_emittedFields).Contains(_1470_callName))) {
            _1465_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1465_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1470_callName));
            RAST._IType _1471_formalType;
            RAST._IType _out78;
            _out78 = (this).GenType(((_1469_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1471_formalType = _out78;
            Dafny.ISequence<RAST._IMatchCase> _1472_cases;
            _1472_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi17 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1473_k = BigInteger.Zero; _1473_k < _hi17; _1473_k++) {
              DAST._IDatatypeCtor _1474_ctor2;
              _1474_ctor2 = ((c).dtor_ctors).Select(_1473_k);
              Dafny.ISequence<Dafny.Rune> _1475_pattern;
              _1475_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1444_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1474_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1476_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1477_hasMatchingField;
              _1477_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1478_patternInner;
              _1478_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1479_isNumeric;
              _1479_isNumeric = false;
              BigInteger _hi18 = new BigInteger(((_1474_ctor2).dtor_args).Count);
              for (BigInteger _1480_l = BigInteger.Zero; _1480_l < _hi18; _1480_l++) {
                DAST._IDatatypeDtor _1481_dtor2;
                _1481_dtor2 = ((_1474_ctor2).dtor_args).Select(_1480_l);
                Dafny.ISequence<Dafny.Rune> _1482_patternName;
                _1482_patternName = DCOMP.__default.escapeVar(((_1481_dtor2).dtor_formal).dtor_name);
                if (((_1480_l).Sign == 0) && ((_1482_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1479_isNumeric = true;
                }
                if (_1479_isNumeric) {
                  _1482_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1481_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1480_l)));
                }
                if (object.Equals(((_1469_dtor).dtor_formal).dtor_name, ((_1481_dtor2).dtor_formal).dtor_name)) {
                  _1477_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1482_patternName);
                }
                _1478_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1478_patternInner, _1482_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1479_isNumeric) {
                _1475_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1475_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1478_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1475_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1475_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1478_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1477_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1476_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1477_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1476_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1477_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1476_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _1483_ctorMatch;
              _1483_ctorMatch = RAST.MatchCase.create(_1475_pattern, RAST.Expr.create_RawExpr(_1476_rhs));
              _1472_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1472_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1483_ctorMatch));
            }
            if (((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) && ((new BigInteger((_1458_unusedTypeParams).Count)).Sign == 1)) {
              _1472_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1472_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1444_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _1484_methodBody;
            _1484_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1472_cases);
            _1464_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1464_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1470_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1471_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1484_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1485_coerceTypes;
      _1485_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1486_rCoerceTypeParams;
      _1486_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1487_coerceArguments;
      _1487_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1488_coerceMap;
      _1488_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1489_rCoerceMap;
      _1489_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1490_coerceMapToArg;
      _1490_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1491_types;
        _1491_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi19 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1492_typeI = BigInteger.Zero; _1492_typeI < _hi19; _1492_typeI++) {
          DAST._ITypeArgDecl _1493_typeParam;
          _1493_typeParam = ((c).dtor_typeParams).Select(_1492_typeI);
          DAST._IType _1494_typeArg;
          RAST._ITypeParamDecl _1495_rTypeParamDecl;
          DAST._IType _out79;
          RAST._ITypeParamDecl _out80;
          (this).GenTypeParam(_1493_typeParam, out _out79, out _out80);
          _1494_typeArg = _out79;
          _1495_rTypeParamDecl = _out80;
          RAST._IType _1496_rTypeArg;
          RAST._IType _out81;
          _out81 = (this).GenType(_1494_typeArg, DCOMP.GenTypeContext.@default());
          _1496_rTypeArg = _out81;
          _1491_types = Dafny.Sequence<RAST._IType>.Concat(_1491_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1496_rTypeArg))));
          if (((_1492_typeI) < (new BigInteger((_1446_variances).Count))) && (((_1446_variances).Select(_1492_typeI)).is_Nonvariant)) {
            _1485_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1485_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1496_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1497_coerceTypeParam;
          DAST._ITypeArgDecl _1498_dt__update__tmp_h0 = _1493_typeParam;
          Dafny.ISequence<Dafny.Rune> _1499_dt__update_hname_h0 = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1492_typeI));
          _1497_coerceTypeParam = DAST.TypeArgDecl.create(_1499_dt__update_hname_h0, (_1498_dt__update__tmp_h0).dtor_bounds, (_1498_dt__update__tmp_h0).dtor_variance);
          DAST._IType _1500_coerceTypeArg;
          RAST._ITypeParamDecl _1501_rCoerceTypeParamDecl;
          DAST._IType _out82;
          RAST._ITypeParamDecl _out83;
          (this).GenTypeParam(_1497_coerceTypeParam, out _out82, out _out83);
          _1500_coerceTypeArg = _out82;
          _1501_rCoerceTypeParamDecl = _out83;
          _1488_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1488_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1494_typeArg, _1500_coerceTypeArg)));
          RAST._IType _1502_rCoerceType;
          RAST._IType _out84;
          _out84 = (this).GenType(_1500_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1502_rCoerceType = _out84;
          _1489_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1489_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1496_rTypeArg, _1502_rCoerceType)));
          _1485_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1485_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1502_rCoerceType));
          _1486_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1486_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1501_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1503_coerceFormal;
          _1503_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1492_typeI));
          _1490_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1490_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1496_rTypeArg, _1502_rCoerceType), (RAST.Expr.create_Identifier(_1503_coerceFormal)).Clone())));
          _1487_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1487_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1503_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1496_rTypeArg), _1502_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        if ((new BigInteger((_1458_unusedTypeParams).Count)).Sign == 1) {
          _1445_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1445_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1504_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1504_tpe);
})), _1491_types)))));
        }
      }
      bool _1505_cIsEq;
      _1505_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1505_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1444_datatypeName, _1442_rTypeParamsDecls, _1445_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1442_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1444_datatypeName), _1441_rTypeParams), _1443_whereConstraints, _1464_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1506_printImplBodyCases;
      _1506_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1507_hashImplBodyCases;
      _1507_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1508_coerceImplBodyCases;
      _1508_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi20 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1509_i = BigInteger.Zero; _1509_i < _hi20; _1509_i++) {
        DAST._IDatatypeCtor _1510_ctor;
        _1510_ctor = ((c).dtor_ctors).Select(_1509_i);
        Dafny.ISequence<Dafny.Rune> _1511_ctorMatch;
        _1511_ctorMatch = DCOMP.__default.escapeName((_1510_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1512_modulePrefix;
        if (((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) {
          _1512_modulePrefix = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        } else {
          _1512_modulePrefix = Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."));
        }
        Dafny.ISequence<Dafny.Rune> _1513_ctorName;
        _1513_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1512_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1510_ctor).dtor_name));
        if (((new BigInteger((_1513_ctorName).Count)) >= (new BigInteger(13))) && (((_1513_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1513_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1514_printRhs;
        _1514_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1513_ctorName), (((_1510_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1515_hashRhs;
        _1515_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1516_coerceRhsArgs;
        _1516_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1517_isNumeric;
        _1517_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1518_ctorMatchInner;
        _1518_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi21 = new BigInteger(((_1510_ctor).dtor_args).Count);
        for (BigInteger _1519_j = BigInteger.Zero; _1519_j < _hi21; _1519_j++) {
          DAST._IDatatypeDtor _1520_dtor;
          _1520_dtor = ((_1510_ctor).dtor_args).Select(_1519_j);
          Dafny.ISequence<Dafny.Rune> _1521_patternName;
          _1521_patternName = DCOMP.__default.escapeVar(((_1520_dtor).dtor_formal).dtor_name);
          DAST._IType _1522_formalType;
          _1522_formalType = ((_1520_dtor).dtor_formal).dtor_typ;
          if (((_1519_j).Sign == 0) && ((_1521_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1517_isNumeric = true;
          }
          if (_1517_isNumeric) {
            _1521_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1520_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1519_j)));
          }
          if ((_1522_formalType).is_Arrow) {
            _1515_hashRhs = (_1515_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          } else {
            _1515_hashRhs = (_1515_hashRhs).Then((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1521_patternName), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state")))));
          }
          _1518_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1518_ctorMatchInner, _1521_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1519_j).Sign == 1) {
            _1514_printRhs = (_1514_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1514_printRhs = (_1514_printRhs).Then(RAST.Expr.create_RawExpr((((_1522_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1521_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1523_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1524_formalTpe;
          RAST._IType _out85;
          _out85 = (this).GenType(_1522_formalType, DCOMP.GenTypeContext.@default());
          _1524_formalTpe = _out85;
          DAST._IType _1525_newFormalType;
          _1525_newFormalType = (_1522_formalType).Replace(_1488_coerceMap);
          RAST._IType _1526_newFormalTpe;
          _1526_newFormalTpe = (_1524_formalTpe).ReplaceMap(_1489_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1527_upcastConverter;
          _1527_upcastConverter = (this).UpcastConversionLambda(_1522_formalType, _1524_formalTpe, _1525_newFormalType, _1526_newFormalTpe, _1490_coerceMapToArg);
          if ((_1527_upcastConverter).is_Success) {
            RAST._IExpr _1528_coercionFunction;
            _1528_coercionFunction = (_1527_upcastConverter).dtor_value;
            _1523_coerceRhsArg = (_1528_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1521_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1519_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1444_datatypeName));
            _1523_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1516_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1516_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1521_patternName, _1523_coerceRhsArg)));
        }
        RAST._IExpr _1529_coerceRhs;
        _1529_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1444_datatypeName)).FSel(DCOMP.__default.escapeName((_1510_ctor).dtor_name)), _1516_coerceRhsArgs);
        if (_1517_isNumeric) {
          _1511_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1511_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1518_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1511_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1511_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1518_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1510_ctor).dtor_hasAnyArgs) {
          _1514_printRhs = (_1514_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1514_printRhs = (_1514_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1506_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1506_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1444_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1511_ctorMatch), RAST.Expr.create_Block(_1514_printRhs))));
        _1507_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1507_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1444_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1511_ctorMatch), RAST.Expr.create_Block(_1515_hashRhs))));
        _1508_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1508_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1444_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1511_ctorMatch), RAST.Expr.create_Block(_1529_coerceRhs))));
      }
      if (((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) && ((new BigInteger((_1458_unusedTypeParams).Count)).Sign == 1)) {
        Dafny.ISequence<RAST._IMatchCase> _1530_extraCases;
        _1530_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1444_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _1506_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1506_printImplBodyCases, _1530_extraCases);
        _1507_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1507_hashImplBodyCases, _1530_extraCases);
        _1508_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1508_coerceImplBodyCases, _1530_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1531_defaultConstrainedTypeParams;
      _1531_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1442_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1532_rTypeParamsDeclsWithEq;
      _1532_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1442_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1533_rTypeParamsDeclsWithHash;
      _1533_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1442_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1534_printImplBody;
      _1534_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1506_printImplBodyCases);
      RAST._IExpr _1535_hashImplBody;
      _1535_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1507_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1442_rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug"))).AsType(), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1444_datatypeName), _1441_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType()))), Std.Wrappers.Option<RAST._IType>.create_Some((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Result"))).AsType()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1442_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1444_datatypeName), _1441_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType())), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1534_printImplBody))))))));
      if ((new BigInteger((_1486_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1536_coerceImplBody;
        _1536_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1508_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1442_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1444_datatypeName), _1441_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1486_rCoerceTypeParams, _1487_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1444_datatypeName), _1441_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1444_datatypeName), _1485_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.__default.SelfOwned)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1444_datatypeName), _1485_coerceTypes)), _1536_coerceImplBody))))))))));
      }
      if (_1505_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1532_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1444_datatypeName), _1441_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1533_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1444_datatypeName), _1441_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))).AsType()))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1535_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1537_structName;
        _1537_structName = (RAST.Expr.create_Identifier(_1444_datatypeName)).FSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1538_structAssignments;
        _1538_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi22 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1539_i = BigInteger.Zero; _1539_i < _hi22; _1539_i++) {
          DAST._IDatatypeDtor _1540_dtor;
          _1540_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1539_i);
          _1538_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1538_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(((_1540_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1541_defaultConstrainedTypeParams;
        _1541_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1442_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1542_fullType;
        _1542_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1444_datatypeName), _1441_rTypeParams);
        if (_1505_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1541_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1542_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1542_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1537_structName, _1538_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1442_rTypeParamsDecls, ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).AsType()).Apply1(_1542_fullType), RAST.Type.create_Borrowed(_1542_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        if (((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))) {
          r = RAST.Path.create_Global();
        } else if (((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"))) {
          r = RAST.__default.dafny__runtime;
        } else {
          r = RAST.Path.create_Crate();
        }
        BigInteger _hi23 = new BigInteger((p).Count);
        for (BigInteger _1543_i = BigInteger.Zero; _1543_i < _hi23; _1543_i++) {
          Dafny.ISequence<Dafny.Rune> _1544_name;
          _1544_name = ((p).Select(_1543_i));
          if (escape) {
            _System._ITuple2<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<Dafny.Rune>> _let_tmp_rhs55 = DafnyCompilerRustUtils.__default.DafnyNameToContainingPathAndName(_1544_name, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1545_modules = _let_tmp_rhs55.dtor__0;
            Dafny.ISequence<Dafny.Rune> _1546_finalName = _let_tmp_rhs55.dtor__1;
            BigInteger _hi24 = new BigInteger((_1545_modules).Count);
            for (BigInteger _1547_j = BigInteger.Zero; _1547_j < _hi24; _1547_j++) {
              r = (r).MSel(DCOMP.__default.escapeName(((_1545_modules).Select(_1547_j))));
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1546_finalName));
          } else {
            r = (r).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1544_name)));
          }
        }
      }
      return r;
    }
    public static RAST._IType GenPathType(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IType t = RAST.Type.Default();
      RAST._IPath _1548_p;
      RAST._IPath _out86;
      _out86 = DCOMP.COMP.GenPath(p, true);
      _1548_p = _out86;
      t = (_1548_p).AsType();
      return t;
    }
    public static RAST._IExpr GenPathExpr(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p, bool escape)
    {
      RAST._IExpr e = RAST.Expr.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        e = RAST.__default.self;
        return e;
      }
      RAST._IPath _1549_p;
      RAST._IPath _out87;
      _out87 = DCOMP.COMP.GenPath(p, escape);
      _1549_p = _out87;
      e = (_1549_p).AsExpr();
      return e;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, bool genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi25 = new BigInteger((args).Count);
      for (BigInteger _1550_i = BigInteger.Zero; _1550_i < _hi25; _1550_i++) {
        RAST._IType _1551_genTp;
        RAST._IType _out88;
        _out88 = (this).GenType((args).Select(_1550_i), genTypeContext);
        _1551_genTp = _out88;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1551_genTp));
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
      {
        if (_source76.is_UserDefined) {
          DAST._IResolvedType _1552_resolved = _source76.dtor_resolved;
          {
            RAST._IType _1553_t;
            RAST._IType _out89;
            _out89 = DCOMP.COMP.GenPathType((_1552_resolved).dtor_path);
            _1553_t = _out89;
            Dafny.ISequence<RAST._IType> _1554_typeArgs;
            Dafny.ISequence<RAST._IType> _out90;
            _out90 = (this).GenTypeArgs((_1552_resolved).dtor_typeArgs, false);
            _1554_typeArgs = _out90;
            s = RAST.Type.create_TypeApp(_1553_t, _1554_typeArgs);
            DAST._IResolvedTypeBase _source77 = (_1552_resolved).dtor_kind;
            {
              if (_source77.is_Class) {
                {
                  s = (this).Object(s);
                }
                goto after_match10;
              }
            }
            {
              if (_source77.is_Datatype) {
                {
                  if ((this).IsRcWrapped((_1552_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
                goto after_match10;
              }
            }
            {
              if (_source77.is_Trait) {
                {
                  if (((_1552_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = RAST.__default.AnyTrait;
                  }
                  if (!((genTypeContext))) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
                goto after_match10;
              }
            }
            {
              DAST._IType _1555_base = _source77.dtor_baseType;
              DAST._INewtypeRange _1556_range = _source77.dtor_range;
              bool _1557_erased = _source77.dtor_erase;
              {
                if (_1557_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source78 = DCOMP.COMP.NewtypeRangeToRustType(_1556_range);
                  {
                    if (_source78.is_Some) {
                      RAST._IType _1558_v = _source78.dtor_value;
                      s = _1558_v;
                      goto after_match11;
                    }
                  }
                  {
                    RAST._IType _1559_underlying;
                    RAST._IType _out91;
                    _out91 = (this).GenType(_1555_base, DCOMP.GenTypeContext.@default());
                    _1559_underlying = _out91;
                    s = RAST.Type.create_TSynonym(s, _1559_underlying);
                  }
                after_match11: ;
                }
              }
            }
          after_match10: ;
          }
          goto after_match9;
        }
      }
      {
        if (_source76.is_Object) {
          {
            s = RAST.__default.AnyTrait;
            if (!((genTypeContext))) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
          goto after_match9;
        }
      }
      {
        if (_source76.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1560_types = _source76.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IType> _1561_args;
            _1561_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1562_i;
            _1562_i = BigInteger.Zero;
            while ((_1562_i) < (new BigInteger((_1560_types).Count))) {
              RAST._IType _1563_generated;
              RAST._IType _out92;
              _out92 = (this).GenType((_1560_types).Select(_1562_i), false);
              _1563_generated = _out92;
              _1561_args = Dafny.Sequence<RAST._IType>.Concat(_1561_args, Dafny.Sequence<RAST._IType>.FromElements(_1563_generated));
              _1562_i = (_1562_i) + (BigInteger.One);
            }
            if ((new BigInteger((_1560_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              s = RAST.Type.create_TupleType(_1561_args);
            } else {
              s = RAST.__default.SystemTupleType(_1561_args);
            }
          }
          goto after_match9;
        }
      }
      {
        if (_source76.is_Array) {
          DAST._IType _1564_element = _source76.dtor_element;
          BigInteger _1565_dims = _source76.dtor_dims;
          {
            if ((_1565_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1566_elem;
              RAST._IType _out93;
              _out93 = (this).GenType(_1564_element, false);
              _1566_elem = _out93;
              if ((_1565_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1566_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1567_n;
                _1567_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1565_dims));
                s = (((RAST.__default.dafny__runtime).MSel(_1567_n)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1566_elem));
                s = (this).Object(s);
              }
            }
          }
          goto after_match9;
        }
      }
      {
        if (_source76.is_Seq) {
          DAST._IType _1568_element = _source76.dtor_element;
          {
            RAST._IType _1569_elem;
            RAST._IType _out94;
            _out94 = (this).GenType(_1568_element, false);
            _1569_elem = _out94;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1569_elem));
          }
          goto after_match9;
        }
      }
      {
        if (_source76.is_Set) {
          DAST._IType _1570_element = _source76.dtor_element;
          {
            RAST._IType _1571_elem;
            RAST._IType _out95;
            _out95 = (this).GenType(_1570_element, false);
            _1571_elem = _out95;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1571_elem));
          }
          goto after_match9;
        }
      }
      {
        if (_source76.is_Multiset) {
          DAST._IType _1572_element = _source76.dtor_element;
          {
            RAST._IType _1573_elem;
            RAST._IType _out96;
            _out96 = (this).GenType(_1572_element, false);
            _1573_elem = _out96;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1573_elem));
          }
          goto after_match9;
        }
      }
      {
        if (_source76.is_Map) {
          DAST._IType _1574_key = _source76.dtor_key;
          DAST._IType _1575_value = _source76.dtor_value;
          {
            RAST._IType _1576_keyType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1574_key, false);
            _1576_keyType = _out97;
            RAST._IType _1577_valueType;
            RAST._IType _out98;
            _out98 = (this).GenType(_1575_value, genTypeContext);
            _1577_valueType = _out98;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1576_keyType, _1577_valueType));
          }
          goto after_match9;
        }
      }
      {
        if (_source76.is_MapBuilder) {
          DAST._IType _1578_key = _source76.dtor_key;
          DAST._IType _1579_value = _source76.dtor_value;
          {
            RAST._IType _1580_keyType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1578_key, false);
            _1580_keyType = _out99;
            RAST._IType _1581_valueType;
            RAST._IType _out100;
            _out100 = (this).GenType(_1579_value, genTypeContext);
            _1581_valueType = _out100;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1580_keyType, _1581_valueType));
          }
          goto after_match9;
        }
      }
      {
        if (_source76.is_SetBuilder) {
          DAST._IType _1582_elem = _source76.dtor_element;
          {
            RAST._IType _1583_elemType;
            RAST._IType _out101;
            _out101 = (this).GenType(_1582_elem, false);
            _1583_elemType = _out101;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1583_elemType));
          }
          goto after_match9;
        }
      }
      {
        if (_source76.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1584_args = _source76.dtor_args;
          DAST._IType _1585_result = _source76.dtor_result;
          {
            Dafny.ISequence<RAST._IType> _1586_argTypes;
            _1586_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1587_i;
            _1587_i = BigInteger.Zero;
            while ((_1587_i) < (new BigInteger((_1584_args).Count))) {
              RAST._IType _1588_generated;
              RAST._IType _out102;
              _out102 = (this).GenType((_1584_args).Select(_1587_i), false);
              _1588_generated = _out102;
              _1586_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1586_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1588_generated)));
              _1587_i = (_1587_i) + (BigInteger.One);
            }
            RAST._IType _1589_resultType;
            RAST._IType _out103;
            _out103 = (this).GenType(_1585_result, DCOMP.GenTypeContext.@default());
            _1589_resultType = _out103;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1586_argTypes, _1589_resultType)));
          }
          goto after_match9;
        }
      }
      {
        if (_source76.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source76.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1590_name = _h90;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1590_name));
          goto after_match9;
        }
      }
      {
        if (_source76.is_Primitive) {
          DAST._IPrimitive _1591_p = _source76.dtor_Primitive_a0;
          {
            DAST._IPrimitive _source79 = _1591_p;
            {
              if (_source79.is_Int) {
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).AsType();
                goto after_match12;
              }
            }
            {
              if (_source79.is_Real) {
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"))).AsType();
                goto after_match12;
              }
            }
            {
              if (_source79.is_String) {
                s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType()));
                goto after_match12;
              }
            }
            {
              if (_source79.is_Bool) {
                s = RAST.Type.create_Bool();
                goto after_match12;
              }
            }
            {
              s = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType();
            }
          after_match12: ;
          }
          goto after_match9;
        }
      }
      {
        Dafny.ISequence<Dafny.Rune> _1592_v = _source76.dtor_Passthrough_a0;
        s = RAST.__default.RawType(_1592_v);
      }
    after_match9: ;
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
      for (BigInteger _1593_i = BigInteger.Zero; _1593_i < _hi26; _1593_i++) {
        DAST._IMethod _source80 = (body).Select(_1593_i);
        {
          DAST._IMethod _1594_m = _source80;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source81 = (_1594_m).dtor_overridingPath;
            {
              if (_source81.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1595_p = _source81.dtor_value;
                {
                  Dafny.ISequence<RAST._IImplMember> _1596_existing;
                  _1596_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1595_p)) {
                    _1596_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1595_p);
                  }
                  if (((new BigInteger(((_1594_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1597_genMethod;
                  RAST._IImplMember _out104;
                  _out104 = (this).GenMethod(_1594_m, true, enclosingType, enclosingTypeParams);
                  _1597_genMethod = _out104;
                  _1596_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1596_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1597_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1595_p, _1596_existing)));
                }
                goto after_match14;
              }
            }
            {
              {
                RAST._IImplMember _1598_generated;
                RAST._IImplMember _out105;
                _out105 = (this).GenMethod(_1594_m, forTrait, enclosingType, enclosingTypeParams);
                _1598_generated = _out105;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1598_generated));
              }
            }
          after_match14: ;
          }
        }
      after_match13: ;
      }
    }
    public Dafny.ISequence<RAST._IFormal> GenParams(Dafny.ISequence<DAST._IFormal> @params, bool forLambda)
    {
      Dafny.ISequence<RAST._IFormal> s = Dafny.Sequence<RAST._IFormal>.Empty;
      s = Dafny.Sequence<RAST._IFormal>.FromElements();
      BigInteger _hi27 = new BigInteger((@params).Count);
      for (BigInteger _1599_i = BigInteger.Zero; _1599_i < _hi27; _1599_i++) {
        DAST._IFormal _1600_param;
        _1600_param = (@params).Select(_1599_i);
        RAST._IType _1601_paramType;
        RAST._IType _out106;
        _out106 = (this).GenType((_1600_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1601_paramType = _out106;
        if (((!((_1601_paramType).CanReadWithoutClone())) || (forLambda)) && (!((_1600_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1601_paramType = RAST.Type.create_Borrowed(_1601_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeVar((_1600_param).dtor_name), _1601_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1602_params;
      Dafny.ISequence<RAST._IFormal> _out107;
      _out107 = (this).GenParams((m).dtor_params, false);
      _1602_params = _out107;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1603_paramNames;
      _1603_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1604_paramTypes;
      _1604_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1605_paramI = BigInteger.Zero; _1605_paramI < _hi28; _1605_paramI++) {
        DAST._IFormal _1606_dafny__formal;
        _1606_dafny__formal = ((m).dtor_params).Select(_1605_paramI);
        RAST._IFormal _1607_formal;
        _1607_formal = (_1602_params).Select(_1605_paramI);
        Dafny.ISequence<Dafny.Rune> _1608_name;
        _1608_name = (_1607_formal).dtor_name;
        _1603_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1603_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1608_name));
        _1604_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1604_paramTypes, _1608_name, (_1607_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1609_fnName;
      _1609_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1610_selfIdent;
      _1610_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1611_selfId;
        _1611_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1611_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv2 = enclosingTypeParams;
        DAST._IType _1612_instanceType;
        DAST._IType _source82 = enclosingType;
        {
          if (_source82.is_UserDefined) {
            DAST._IResolvedType _1613_r = _source82.dtor_resolved;
            _1612_instanceType = DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1613_r, _pat_let20_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let20_0, _1614_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv2, _pat_let21_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let21_0, _1615_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1614_dt__update__tmp_h0).dtor_path, _1615_dt__update_htypeArgs_h0, (_1614_dt__update__tmp_h0).dtor_kind, (_1614_dt__update__tmp_h0).dtor_attributes, (_1614_dt__update__tmp_h0).dtor_properMethods, (_1614_dt__update__tmp_h0).dtor_extendedTypes))))));
            goto after_match15;
          }
        }
        {
          _1612_instanceType = enclosingType;
        }
      after_match15: ;
        if (forTrait) {
          RAST._IFormal _1616_selfFormal;
          if ((m).dtor_wasFunction) {
            _1616_selfFormal = RAST.Formal.selfBorrowed;
          } else {
            _1616_selfFormal = RAST.Formal.selfBorrowedMut;
          }
          _1602_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1616_selfFormal), _1602_params);
        } else {
          RAST._IType _1617_tpe;
          RAST._IType _out108;
          _out108 = (this).GenType(_1612_instanceType, DCOMP.GenTypeContext.@default());
          _1617_tpe = _out108;
          if ((_1611_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            if (((this).ObjectType).is_RcMut) {
              _1617_tpe = RAST.Type.create_Borrowed(_1617_tpe);
            }
          } else if ((_1611_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1617_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1617_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1617_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _1617_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.__default.SelfOwned));
              } else {
                _1617_tpe = RAST.Type.create_Borrowed(RAST.__default.SelfOwned);
              }
            }
          }
          _1602_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1611_selfId, _1617_tpe)), _1602_params);
        }
        _1610_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1611_selfId, _1612_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1618_retTypeArgs;
      _1618_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1619_typeI;
      _1619_typeI = BigInteger.Zero;
      while ((_1619_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1620_typeExpr;
        RAST._IType _out109;
        _out109 = (this).GenType(((m).dtor_outTypes).Select(_1619_typeI), DCOMP.GenTypeContext.@default());
        _1620_typeExpr = _out109;
        _1618_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1618_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1620_typeExpr));
        _1619_typeI = (_1619_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1621_visibility;
      if (forTrait) {
        _1621_visibility = RAST.Visibility.create_PRIV();
      } else {
        _1621_visibility = RAST.Visibility.create_PUB();
      }
      Dafny.ISequence<DAST._ITypeArgDecl> _1622_typeParamsFiltered;
      _1622_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi29 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1623_typeParamI = BigInteger.Zero; _1623_typeParamI < _hi29; _1623_typeParamI++) {
        DAST._ITypeArgDecl _1624_typeParam;
        _1624_typeParam = ((m).dtor_typeParams).Select(_1623_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1624_typeParam).dtor_name)))) {
          _1622_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1622_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1624_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1625_typeParams;
      _1625_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1622_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi30 = new BigInteger((_1622_typeParamsFiltered).Count);
        for (BigInteger _1626_i = BigInteger.Zero; _1626_i < _hi30; _1626_i++) {
          DAST._IType _1627_typeArg;
          RAST._ITypeParamDecl _1628_rTypeParamDecl;
          DAST._IType _out110;
          RAST._ITypeParamDecl _out111;
          (this).GenTypeParam((_1622_typeParamsFiltered).Select(_1626_i), out _out110, out _out111);
          _1627_typeArg = _out110;
          _1628_rTypeParamDecl = _out111;
          RAST._ITypeParamDecl _1629_dt__update__tmp_h1 = _1628_rTypeParamDecl;
          Dafny.ISequence<RAST._IType> _1630_dt__update_hconstraints_h0 = (_1628_rTypeParamDecl).dtor_constraints;
          _1628_rTypeParamDecl = RAST.TypeParamDecl.create((_1629_dt__update__tmp_h1).dtor_name, _1630_dt__update_hconstraints_h0);
          _1625_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1625_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1628_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1631_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1632_env = DCOMP.Environment.Default();
      RAST._IExpr _1633_preBody;
      _1633_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1634_preAssignNames;
      _1634_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1635_preAssignTypes;
      _1635_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1636_earlyReturn;
        _1636_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source83 = (m).dtor_outVars;
        {
          if (_source83.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1637_outVars = _source83.dtor_value;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1636_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi31 = new BigInteger((_1637_outVars).Count);
                for (BigInteger _1638_outI = BigInteger.Zero; _1638_outI < _hi31; _1638_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1639_outVar;
                  _1639_outVar = (_1637_outVars).Select(_1638_outI);
                  Dafny.ISequence<Dafny.Rune> _1640_outName;
                  _1640_outName = DCOMP.__default.escapeVar(_1639_outVar);
                  Dafny.ISequence<Dafny.Rune> _1641_tracker__name;
                  _1641_tracker__name = DCOMP.__default.AddAssignedPrefix(_1640_outName);
                  _1634_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1634_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1641_tracker__name));
                  _1635_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1635_preAssignTypes, _1641_tracker__name, RAST.Type.create_Bool());
                  _1633_preBody = (_1633_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1641_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1642_tupleArgs;
                _1642_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi32 = new BigInteger((_1637_outVars).Count);
                for (BigInteger _1643_outI = BigInteger.Zero; _1643_outI < _hi32; _1643_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1644_outVar;
                  _1644_outVar = (_1637_outVars).Select(_1643_outI);
                  RAST._IType _1645_outType;
                  RAST._IType _out112;
                  _out112 = (this).GenType(((m).dtor_outTypes).Select(_1643_outI), DCOMP.GenTypeContext.@default());
                  _1645_outType = _out112;
                  Dafny.ISequence<Dafny.Rune> _1646_outName;
                  _1646_outName = DCOMP.__default.escapeVar(_1644_outVar);
                  _1603_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1603_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1646_outName));
                  RAST._IType _1647_outMaybeType;
                  if ((_1645_outType).CanReadWithoutClone()) {
                    _1647_outMaybeType = _1645_outType;
                  } else {
                    _1647_outMaybeType = RAST.__default.MaybePlaceboType(_1645_outType);
                  }
                  _1604_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1604_paramTypes, _1646_outName, _1647_outMaybeType);
                  _1642_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1642_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1646_outName));
                }
                _1636_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_1642_tupleArgs);
              }
            }
            goto after_match16;
          }
        }
        {
        }
      after_match16: ;
        _1632_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1634_preAssignNames, _1603_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1635_preAssignTypes, _1604_paramTypes));
        RAST._IExpr _1648_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1649___v71;
        DCOMP._IEnvironment _1650___v72;
        RAST._IExpr _out113;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out114;
        DCOMP._IEnvironment _out115;
        (this).GenStmts((m).dtor_body, _1610_selfIdent, _1632_env, true, _1636_earlyReturn, out _out113, out _out114, out _out115);
        _1648_body = _out113;
        _1649___v71 = _out114;
        _1650___v72 = _out115;
        _1631_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1633_preBody).Then(_1648_body));
      } else {
        _1632_env = DCOMP.Environment.create(_1603_paramNames, _1604_paramTypes);
        _1631_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1621_visibility, RAST.Fn.create(_1609_fnName, _1625_typeParams, _1602_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1618_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1618_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1618_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1631_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1651_declarations;
      _1651_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1652_i;
      _1652_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1653_stmts;
      _1653_stmts = stmts;
      while ((_1652_i) < (new BigInteger((_1653_stmts).Count))) {
        DAST._IStatement _1654_stmt;
        _1654_stmt = (_1653_stmts).Select(_1652_i);
        DAST._IStatement _source84 = _1654_stmt;
        {
          if (_source84.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1655_name = _source84.dtor_name;
            DAST._IType _1656_optType = _source84.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source84.dtor_maybeValue;
            if (maybeValue0.is_None) {
              if (((_1652_i) + (BigInteger.One)) < (new BigInteger((_1653_stmts).Count))) {
                DAST._IStatement _source85 = (_1653_stmts).Select((_1652_i) + (BigInteger.One));
                {
                  if (_source85.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source85.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> _1657_name2 = lhs0.dtor_ident;
                      DAST._IExpression _1658_rhs = _source85.dtor_value;
                      if (object.Equals(_1657_name2, _1655_name)) {
                        _1653_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1653_stmts).Subsequence(BigInteger.Zero, _1652_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1655_name, _1656_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1658_rhs)))), (_1653_stmts).Drop((_1652_i) + (new BigInteger(2))));
                        _1654_stmt = (_1653_stmts).Select(_1652_i);
                      }
                      goto after_match18;
                    }
                  }
                }
                {
                }
              after_match18: ;
              }
              goto after_match17;
            }
          }
        }
        {
        }
      after_match17: ;
        RAST._IExpr _1659_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1660_recIdents;
        DCOMP._IEnvironment _1661_newEnv2;
        RAST._IExpr _out116;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out117;
        DCOMP._IEnvironment _out118;
        (this).GenStmt(_1654_stmt, selfIdent, newEnv, (isLast) && ((_1652_i) == ((new BigInteger((_1653_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out116, out _out117, out _out118);
        _1659_stmtExpr = _out116;
        _1660_recIdents = _out117;
        _1661_newEnv2 = _out118;
        newEnv = _1661_newEnv2;
        DAST._IStatement _source86 = _1654_stmt;
        {
          if (_source86.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1662_name = _source86.dtor_name;
            {
              _1651_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1651_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_1662_name)));
            }
            goto after_match19;
          }
        }
        {
        }
      after_match19: ;
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1660_recIdents, _1651_declarations));
        generated = (generated).Then(_1659_stmtExpr);
        _1652_i = (_1652_i) + (BigInteger.One);
        if ((_1659_stmtExpr).is_Return) {
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
      {
        if (_source87.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1663_id = _source87.dtor_ident;
          {
            Dafny.ISequence<Dafny.Rune> _1664_idRust;
            _1664_idRust = DCOMP.__default.escapeVar(_1663_id);
            if (((env).IsBorrowed(_1664_idRust)) || ((env).IsBorrowedMut(_1664_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1664_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1664_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1664_idRust);
            needsIIFE = false;
          }
          goto after_match20;
        }
      }
      {
        if (_source87.is_Select) {
          DAST._IExpression _1665_on = _source87.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1666_field = _source87.dtor_field;
          {
            Dafny.ISequence<Dafny.Rune> _1667_fieldName;
            _1667_fieldName = DCOMP.__default.escapeVar(_1666_field);
            RAST._IExpr _1668_onExpr;
            DCOMP._IOwnership _1669_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1670_recIdents;
            RAST._IExpr _out119;
            DCOMP._IOwnership _out120;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
            (this).GenExpr(_1665_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out119, out _out120, out _out121);
            _1668_onExpr = _out119;
            _1669_onOwned = _out120;
            _1670_recIdents = _out121;
            RAST._IExpr _source88 = _1668_onExpr;
            {
              bool disjunctiveMatch11 = false;
              if (_source88.is_Call) {
                RAST._IExpr obj2 = _source88.dtor_obj;
                if (obj2.is_Select) {
                  RAST._IExpr obj3 = obj2.dtor_obj;
                  if (obj3.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name4 = obj3.dtor_name;
                    if (object.Equals(name4, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      Dafny.ISequence<Dafny.Rune> name5 = obj2.dtor_name;
                      if (object.Equals(name5, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                        disjunctiveMatch11 = true;
                      }
                    }
                  }
                }
              }
              if (_source88.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name6 = _source88.dtor_name;
                if (object.Equals(name6, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch11 = true;
                }
              }
              if (_source88.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op14 = _source88.dtor_op1;
                if (object.Equals(op14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying4 = _source88.dtor_underlying;
                  if (underlying4.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name7 = underlying4.dtor_name;
                    if (object.Equals(name7, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      disjunctiveMatch11 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch11) {
                Dafny.ISequence<Dafny.Rune> _1671_isAssignedVar;
                _1671_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1667_fieldName);
                if (((newEnv).dtor_names).Contains(_1671_isAssignedVar)) {
                  generated = (((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1667_fieldName), RAST.Expr.create_Identifier(_1671_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1671_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1671_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1667_fieldName, rhs);
                }
                goto after_match21;
              }
            }
            {
              if (!object.Equals(_1668_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1668_onExpr = ((this).modify__macro).Apply1(_1668_onExpr);
              }
              generated = RAST.__default.AssignMember(_1668_onExpr, _1667_fieldName, rhs);
            }
          after_match21: ;
            readIdents = _1670_recIdents;
            needsIIFE = false;
          }
          goto after_match20;
        }
      }
      {
        DAST._IExpression _1672_on = _source87.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1673_indices = _source87.dtor_indices;
        {
          RAST._IExpr _1674_onExpr;
          DCOMP._IOwnership _1675_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1676_recIdents;
          RAST._IExpr _out122;
          DCOMP._IOwnership _out123;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
          (this).GenExpr(_1672_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out122, out _out123, out _out124);
          _1674_onExpr = _out122;
          _1675_onOwned = _out123;
          _1676_recIdents = _out124;
          readIdents = _1676_recIdents;
          _1674_onExpr = ((this).modify__macro).Apply1(_1674_onExpr);
          RAST._IExpr _1677_r;
          _1677_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1678_indicesExpr;
          _1678_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi33 = new BigInteger((_1673_indices).Count);
          for (BigInteger _1679_i = BigInteger.Zero; _1679_i < _hi33; _1679_i++) {
            RAST._IExpr _1680_idx;
            DCOMP._IOwnership _1681___v81;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1682_recIdentsIdx;
            RAST._IExpr _out125;
            DCOMP._IOwnership _out126;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out127;
            (this).GenExpr((_1673_indices).Select(_1679_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out125, out _out126, out _out127);
            _1680_idx = _out125;
            _1681___v81 = _out126;
            _1682_recIdentsIdx = _out127;
            Dafny.ISequence<Dafny.Rune> _1683_varName;
            _1683_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1679_i));
            _1678_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1678_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1683_varName)));
            _1677_r = (_1677_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1683_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1680_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1682_recIdentsIdx);
          }
          if ((new BigInteger((_1673_indices).Count)) > (BigInteger.One)) {
            _1674_onExpr = (_1674_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1684_rhs;
          _1684_rhs = rhs;
          var _pat_let_tv3 = env;
          if (((_1674_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1674_onExpr).LhsIdentifierName(), _pat_let22_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let22_0, _1685_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv3).GetType(_1685_name), _pat_let23_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let23_0, _1686_tpe => ((_1686_tpe).is_Some) && (((_1686_tpe).dtor_value).IsUninitArray())))))))) {
            _1684_rhs = RAST.__default.MaybeUninitNew(_1684_rhs);
          }
          generated = (_1677_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1674_onExpr, _1678_indicesExpr)), _1684_rhs));
          needsIIFE = true;
        }
      }
    after_match20: ;
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source89 = stmt;
      {
        if (_source89.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1687_fields = _source89.dtor_fields;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi34 = new BigInteger((_1687_fields).Count);
            for (BigInteger _1688_i = BigInteger.Zero; _1688_i < _hi34; _1688_i++) {
              DAST._IFormal _1689_field;
              _1689_field = (_1687_fields).Select(_1688_i);
              Dafny.ISequence<Dafny.Rune> _1690_fieldName;
              _1690_fieldName = DCOMP.__default.escapeVar((_1689_field).dtor_name);
              RAST._IType _1691_fieldTyp;
              RAST._IType _out128;
              _out128 = (this).GenType((_1689_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1691_fieldTyp = _out128;
              Dafny.ISequence<Dafny.Rune> _1692_isAssignedVar;
              _1692_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1690_fieldName);
              if (((newEnv).dtor_names).Contains(_1692_isAssignedVar)) {
                RAST._IExpr _1693_rhs;
                DCOMP._IOwnership _1694___v82;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1695___v83;
                RAST._IExpr _out129;
                DCOMP._IOwnership _out130;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out131;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1689_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out129, out _out130, out _out131);
                _1693_rhs = _out129;
                _1694___v82 = _out130;
                _1695___v83 = _out131;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1692_isAssignedVar));
                generated = (generated).Then((((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1690_fieldName), RAST.Expr.create_Identifier(_1692_isAssignedVar), _1693_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1692_isAssignedVar);
              }
            }
          }
          goto after_match22;
        }
      }
      {
        if (_source89.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1696_name = _source89.dtor_name;
          DAST._IType _1697_typ = _source89.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source89.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1698_expression = maybeValue1.dtor_value;
            {
              RAST._IType _1699_tpe;
              RAST._IType _out132;
              _out132 = (this).GenType(_1697_typ, DCOMP.GenTypeContext.@default());
              _1699_tpe = _out132;
              Dafny.ISequence<Dafny.Rune> _1700_varName;
              _1700_varName = DCOMP.__default.escapeVar(_1696_name);
              bool _1701_hasCopySemantics;
              _1701_hasCopySemantics = (_1699_tpe).CanReadWithoutClone();
              if (((_1698_expression).is_InitializationValue) && (!(_1701_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1700_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.MaybePlaceboPath).AsExpr()).ApplyType1(_1699_tpe)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1700_varName, RAST.__default.MaybePlaceboType(_1699_tpe));
              } else {
                RAST._IExpr _1702_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1703_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1698_expression).is_InitializationValue) && ((_1699_tpe).IsObjectOrPointer())) {
                  _1702_expr = (_1699_tpe).ToNullExpr();
                  _1703_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1704_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out133;
                  DCOMP._IOwnership _out134;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out135;
                  (this).GenExpr(_1698_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out133, out _out134, out _out135);
                  _1702_expr = _out133;
                  _1704_exprOwnership = _out134;
                  _1703_recIdents = _out135;
                }
                readIdents = _1703_recIdents;
                if ((_1698_expression).is_NewUninitArray) {
                  _1699_tpe = (_1699_tpe).TypeAtInitialization();
                } else {
                  _1699_tpe = _1699_tpe;
                }
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1700_varName, Std.Wrappers.Option<RAST._IType>.create_Some(_1699_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1702_expr));
                newEnv = (env).AddAssigned(_1700_varName, _1699_tpe);
              }
            }
            goto after_match22;
          }
        }
      }
      {
        if (_source89.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1705_name = _source89.dtor_name;
          DAST._IType _1706_typ = _source89.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source89.dtor_maybeValue;
          if (maybeValue2.is_None) {
            {
              DAST._IStatement _1707_newStmt;
              _1707_newStmt = DAST.Statement.create_DeclareVar(_1705_name, _1706_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1706_typ)));
              RAST._IExpr _out136;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out137;
              DCOMP._IEnvironment _out138;
              (this).GenStmt(_1707_newStmt, selfIdent, env, isLast, earlyReturn, out _out136, out _out137, out _out138);
              generated = _out136;
              readIdents = _out137;
              newEnv = _out138;
            }
            goto after_match22;
          }
        }
      }
      {
        if (_source89.is_Assign) {
          DAST._IAssignLhs _1708_lhs = _source89.dtor_lhs;
          DAST._IExpression _1709_expression = _source89.dtor_value;
          {
            RAST._IExpr _1710_exprGen;
            DCOMP._IOwnership _1711___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1712_exprIdents;
            RAST._IExpr _out139;
            DCOMP._IOwnership _out140;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
            (this).GenExpr(_1709_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out139, out _out140, out _out141);
            _1710_exprGen = _out139;
            _1711___v84 = _out140;
            _1712_exprIdents = _out141;
            if ((_1708_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1713_rustId;
              _1713_rustId = DCOMP.__default.escapeVar((_1708_lhs).dtor_ident);
              Std.Wrappers._IOption<RAST._IType> _1714_tpe;
              _1714_tpe = (env).GetType(_1713_rustId);
              if (((_1714_tpe).is_Some) && ((((_1714_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1710_exprGen = RAST.__default.MaybePlacebo(_1710_exprGen);
              }
            }
            if (((_1708_lhs).is_Index) && (((_1708_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1715_rustId;
              _1715_rustId = DCOMP.__default.escapeVar(((_1708_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1716_tpe;
              _1716_tpe = (env).GetType(_1715_rustId);
              if (((_1716_tpe).is_Some) && ((((_1716_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1710_exprGen = RAST.__default.MaybeUninitNew(_1710_exprGen);
              }
            }
            RAST._IExpr _1717_lhsGen;
            bool _1718_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1719_recIdents;
            DCOMP._IEnvironment _1720_resEnv;
            RAST._IExpr _out142;
            bool _out143;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out144;
            DCOMP._IEnvironment _out145;
            (this).GenAssignLhs(_1708_lhs, _1710_exprGen, selfIdent, env, out _out142, out _out143, out _out144, out _out145);
            _1717_lhsGen = _out142;
            _1718_needsIIFE = _out143;
            _1719_recIdents = _out144;
            _1720_resEnv = _out145;
            generated = _1717_lhsGen;
            newEnv = _1720_resEnv;
            if (_1718_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1719_recIdents, _1712_exprIdents);
          }
          goto after_match22;
        }
      }
      {
        if (_source89.is_If) {
          DAST._IExpression _1721_cond = _source89.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1722_thnDafny = _source89.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1723_elsDafny = _source89.dtor_els;
          {
            RAST._IExpr _1724_cond;
            DCOMP._IOwnership _1725___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1726_recIdents;
            RAST._IExpr _out146;
            DCOMP._IOwnership _out147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
            (this).GenExpr(_1721_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out146, out _out147, out _out148);
            _1724_cond = _out146;
            _1725___v85 = _out147;
            _1726_recIdents = _out148;
            Dafny.ISequence<Dafny.Rune> _1727_condString;
            _1727_condString = (_1724_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1726_recIdents;
            RAST._IExpr _1728_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1729_thnIdents;
            DCOMP._IEnvironment _1730_thnEnv;
            RAST._IExpr _out149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out150;
            DCOMP._IEnvironment _out151;
            (this).GenStmts(_1722_thnDafny, selfIdent, env, isLast, earlyReturn, out _out149, out _out150, out _out151);
            _1728_thn = _out149;
            _1729_thnIdents = _out150;
            _1730_thnEnv = _out151;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1729_thnIdents);
            RAST._IExpr _1731_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1732_elsIdents;
            DCOMP._IEnvironment _1733_elsEnv;
            RAST._IExpr _out152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
            DCOMP._IEnvironment _out154;
            (this).GenStmts(_1723_elsDafny, selfIdent, env, isLast, earlyReturn, out _out152, out _out153, out _out154);
            _1731_els = _out152;
            _1732_elsIdents = _out153;
            _1733_elsEnv = _out154;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1732_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1724_cond, _1728_thn, _1731_els);
          }
          goto after_match22;
        }
      }
      {
        if (_source89.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1734_lbl = _source89.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1735_body = _source89.dtor_body;
          {
            RAST._IExpr _1736_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1737_bodyIdents;
            DCOMP._IEnvironment _1738_env2;
            RAST._IExpr _out155;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out156;
            DCOMP._IEnvironment _out157;
            (this).GenStmts(_1735_body, selfIdent, env, isLast, earlyReturn, out _out155, out _out156, out _out157);
            _1736_body = _out155;
            _1737_bodyIdents = _out156;
            _1738_env2 = _out157;
            readIdents = _1737_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1734_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1736_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        if (_source89.is_While) {
          DAST._IExpression _1739_cond = _source89.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1740_body = _source89.dtor_body;
          {
            RAST._IExpr _1741_cond;
            DCOMP._IOwnership _1742___v86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1743_recIdents;
            RAST._IExpr _out158;
            DCOMP._IOwnership _out159;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out160;
            (this).GenExpr(_1739_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out158, out _out159, out _out160);
            _1741_cond = _out158;
            _1742___v86 = _out159;
            _1743_recIdents = _out160;
            readIdents = _1743_recIdents;
            RAST._IExpr _1744_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1745_bodyIdents;
            DCOMP._IEnvironment _1746_bodyEnv;
            RAST._IExpr _out161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out162;
            DCOMP._IEnvironment _out163;
            (this).GenStmts(_1740_body, selfIdent, env, false, earlyReturn, out _out161, out _out162, out _out163);
            _1744_bodyExpr = _out161;
            _1745_bodyIdents = _out162;
            _1746_bodyEnv = _out163;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1745_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1741_cond), _1744_bodyExpr);
          }
          goto after_match22;
        }
      }
      {
        if (_source89.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1747_boundName = _source89.dtor_boundName;
          DAST._IType _1748_boundType = _source89.dtor_boundType;
          DAST._IExpression _1749_overExpr = _source89.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1750_body = _source89.dtor_body;
          {
            RAST._IExpr _1751_over;
            DCOMP._IOwnership _1752___v87;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1753_recIdents;
            RAST._IExpr _out164;
            DCOMP._IOwnership _out165;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out166;
            (this).GenExpr(_1749_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out164, out _out165, out _out166);
            _1751_over = _out164;
            _1752___v87 = _out165;
            _1753_recIdents = _out166;
            if (((_1749_overExpr).is_MapBoundedPool) || ((_1749_overExpr).is_SetBoundedPool)) {
              _1751_over = ((_1751_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1754_boundTpe;
            RAST._IType _out167;
            _out167 = (this).GenType(_1748_boundType, DCOMP.GenTypeContext.@default());
            _1754_boundTpe = _out167;
            readIdents = _1753_recIdents;
            Dafny.ISequence<Dafny.Rune> _1755_boundRName;
            _1755_boundRName = DCOMP.__default.escapeVar(_1747_boundName);
            RAST._IExpr _1756_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1757_bodyIdents;
            DCOMP._IEnvironment _1758_bodyEnv;
            RAST._IExpr _out168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out169;
            DCOMP._IEnvironment _out170;
            (this).GenStmts(_1750_body, selfIdent, (env).AddAssigned(_1755_boundRName, _1754_boundTpe), false, earlyReturn, out _out168, out _out169, out _out170);
            _1756_bodyExpr = _out168;
            _1757_bodyIdents = _out169;
            _1758_bodyEnv = _out170;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1757_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1755_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1755_boundRName, _1751_over, _1756_bodyExpr);
          }
          goto after_match22;
        }
      }
      {
        if (_source89.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1759_toLabel = _source89.dtor_toLabel;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source90 = _1759_toLabel;
            {
              if (_source90.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1760_lbl = _source90.dtor_value;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1760_lbl)));
                }
                goto after_match23;
              }
            }
            {
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
          after_match23: ;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        if (_source89.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1761_body = _source89.dtor_body;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1762_selfClone;
              DCOMP._IOwnership _1763___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1764___v89;
              RAST._IExpr _out171;
              DCOMP._IOwnership _out172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out171, out _out172, out _out173);
              _1762_selfClone = _out171;
              _1763___v88 = _out172;
              _1764___v89 = _out173;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1762_selfClone)));
            }
            newEnv = env;
            BigInteger _hi35 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1765_paramI = BigInteger.Zero; _1765_paramI < _hi35; _1765_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1766_param;
              _1766_param = ((env).dtor_names).Select(_1765_paramI);
              RAST._IExpr _1767_paramInit;
              DCOMP._IOwnership _1768___v90;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1769___v91;
              RAST._IExpr _out174;
              DCOMP._IOwnership _out175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out176;
              (this).GenIdent(_1766_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out174, out _out175, out _out176);
              _1767_paramInit = _out174;
              _1768___v90 = _out175;
              _1769___v91 = _out176;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1766_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1767_paramInit)));
              if (((env).dtor_types).Contains(_1766_param)) {
                RAST._IType _1770_declaredType;
                _1770_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1766_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1766_param, _1770_declaredType);
              }
            }
            RAST._IExpr _1771_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1772_bodyIdents;
            DCOMP._IEnvironment _1773_bodyEnv;
            RAST._IExpr _out177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out178;
            DCOMP._IEnvironment _out179;
            (this).GenStmts(_1761_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out177, out _out178, out _out179);
            _1771_bodyExpr = _out177;
            _1772_bodyIdents = _out178;
            _1773_bodyEnv = _out179;
            readIdents = _1772_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1771_bodyExpr)));
          }
          goto after_match22;
        }
      }
      {
        if (_source89.is_JumpTailCallStart) {
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        if (_source89.is_Call) {
          DAST._IExpression _1774_on = _source89.dtor_on;
          DAST._ICallName _1775_name = _source89.dtor_callName;
          Dafny.ISequence<DAST._IType> _1776_typeArgs = _source89.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1777_args = _source89.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1778_maybeOutVars = _source89.dtor_outs;
          {
            Dafny.ISequence<RAST._IExpr> _1779_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1780_recIdents;
            Dafny.ISequence<RAST._IType> _1781_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1782_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out181;
            Dafny.ISequence<RAST._IType> _out182;
            Std.Wrappers._IOption<DAST._IResolvedType> _out183;
            (this).GenArgs(selfIdent, _1775_name, _1776_typeArgs, _1777_args, env, out _out180, out _out181, out _out182, out _out183);
            _1779_argExprs = _out180;
            _1780_recIdents = _out181;
            _1781_typeExprs = _out182;
            _1782_fullNameQualifier = _out183;
            readIdents = _1780_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source91 = _1782_fullNameQualifier;
            {
              if (_source91.is_Some) {
                DAST._IResolvedType value9 = _source91.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1783_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1784_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1785_base = value9.dtor_kind;
                RAST._IExpr _1786_fullPath;
                RAST._IExpr _out184;
                _out184 = DCOMP.COMP.GenPathExpr(_1783_path, true);
                _1786_fullPath = _out184;
                Dafny.ISequence<RAST._IType> _1787_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out185;
                _out185 = (this).GenTypeArgs(_1784_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1787_onTypeExprs = _out185;
                RAST._IExpr _1788_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1789_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1790_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1785_base).is_Trait) || ((_1785_base).is_Class)) {
                  RAST._IExpr _out186;
                  DCOMP._IOwnership _out187;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out188;
                  (this).GenExpr(_1774_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out186, out _out187, out _out188);
                  _1788_onExpr = _out186;
                  _1789_recOwnership = _out187;
                  _1790_recIdents = _out188;
                  _1788_onExpr = ((this).modify__macro).Apply1(_1788_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1790_recIdents);
                } else {
                  RAST._IExpr _out189;
                  DCOMP._IOwnership _out190;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out191;
                  (this).GenExpr(_1774_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out189, out _out190, out _out191);
                  _1788_onExpr = _out189;
                  _1789_recOwnership = _out190;
                  _1790_recIdents = _out191;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1790_recIdents);
                }
                generated = ((((_1786_fullPath).ApplyType(_1787_onTypeExprs)).FSel(DCOMP.__default.escapeName((_1775_name).dtor_name))).ApplyType(_1781_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1788_onExpr), _1779_argExprs));
                goto after_match24;
              }
            }
            {
              RAST._IExpr _1791_onExpr;
              DCOMP._IOwnership _1792___v96;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1793_enclosingIdents;
              RAST._IExpr _out192;
              DCOMP._IOwnership _out193;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out194;
              (this).GenExpr(_1774_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out192, out _out193, out _out194);
              _1791_onExpr = _out192;
              _1792___v96 = _out193;
              _1793_enclosingIdents = _out194;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1793_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1794_renderedName;
              _1794_renderedName = (this).GetMethodName(_1774_on, _1775_name);
              DAST._IExpression _source92 = _1774_on;
              {
                bool disjunctiveMatch12 = false;
                if (_source92.is_Companion) {
                  disjunctiveMatch12 = true;
                }
                if (_source92.is_ExternCompanion) {
                  disjunctiveMatch12 = true;
                }
                if (disjunctiveMatch12) {
                  {
                    _1791_onExpr = (_1791_onExpr).FSel(_1794_renderedName);
                  }
                  goto after_match25;
                }
              }
              {
                {
                  if (!object.Equals(_1791_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source93 = _1775_name;
                    {
                      if (_source93.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source93.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1795_tpe = onType0.dtor_value;
                          RAST._IType _1796_typ;
                          RAST._IType _out195;
                          _out195 = (this).GenType(_1795_tpe, DCOMP.GenTypeContext.@default());
                          _1796_typ = _out195;
                          if (((_1796_typ).IsObjectOrPointer()) && (!object.Equals(_1791_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1791_onExpr = ((this).modify__macro).Apply1(_1791_onExpr);
                          }
                          goto after_match26;
                        }
                      }
                    }
                    {
                    }
                  after_match26: ;
                  }
                  _1791_onExpr = (_1791_onExpr).Sel(_1794_renderedName);
                }
              }
            after_match25: ;
              generated = ((_1791_onExpr).ApplyType(_1781_typeExprs)).Apply(_1779_argExprs);
            }
          after_match24: ;
            if (((_1778_maybeOutVars).is_Some) && ((new BigInteger(((_1778_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1797_outVar;
              _1797_outVar = DCOMP.__default.escapeVar(((_1778_maybeOutVars).dtor_value).Select(BigInteger.Zero));
              if (!((env).CanReadWithoutClone(_1797_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1797_outVar, generated);
            } else if (((_1778_maybeOutVars).is_None) || ((new BigInteger(((_1778_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1798_tmpVar;
              _1798_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1799_tmpId;
              _1799_tmpId = RAST.Expr.create_Identifier(_1798_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1798_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1800_outVars;
              _1800_outVars = (_1778_maybeOutVars).dtor_value;
              BigInteger _hi36 = new BigInteger((_1800_outVars).Count);
              for (BigInteger _1801_outI = BigInteger.Zero; _1801_outI < _hi36; _1801_outI++) {
                Dafny.ISequence<Dafny.Rune> _1802_outVar;
                _1802_outVar = DCOMP.__default.escapeVar((_1800_outVars).Select(_1801_outI));
                RAST._IExpr _1803_rhs;
                _1803_rhs = (_1799_tmpId).Sel(Std.Strings.__default.OfNat(_1801_outI));
                if (!((env).CanReadWithoutClone(_1802_outVar))) {
                  _1803_rhs = RAST.__default.MaybePlacebo(_1803_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1802_outVar, _1803_rhs));
              }
            }
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        if (_source89.is_Return) {
          DAST._IExpression _1804_exprDafny = _source89.dtor_expr;
          {
            RAST._IExpr _1805_expr;
            DCOMP._IOwnership _1806___v106;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1807_recIdents;
            RAST._IExpr _out196;
            DCOMP._IOwnership _out197;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out198;
            (this).GenExpr(_1804_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out196, out _out197, out _out198);
            _1805_expr = _out196;
            _1806___v106 = _out197;
            _1807_recIdents = _out198;
            readIdents = _1807_recIdents;
            if (isLast) {
              generated = _1805_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1805_expr));
            }
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        if (_source89.is_EarlyReturn) {
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source94 = earlyReturn;
            {
              if (_source94.is_None) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
                goto after_match27;
              }
            }
            {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1808_rustIdents = _source94.dtor_value;
              Dafny.ISequence<RAST._IExpr> _1809_tupleArgs;
              _1809_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi37 = new BigInteger((_1808_rustIdents).Count);
              for (BigInteger _1810_i = BigInteger.Zero; _1810_i < _hi37; _1810_i++) {
                RAST._IExpr _1811_rIdent;
                DCOMP._IOwnership _1812___v107;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1813___v108;
                RAST._IExpr _out199;
                DCOMP._IOwnership _out200;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
                (this).GenIdent((_1808_rustIdents).Select(_1810_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out199, out _out200, out _out201);
                _1811_rIdent = _out199;
                _1812___v107 = _out200;
                _1813___v108 = _out201;
                _1809_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1809_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1811_rIdent));
              }
              if ((new BigInteger((_1809_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1809_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1809_tupleArgs)));
              }
            }
          after_match27: ;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        if (_source89.is_Halt) {
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
          goto after_match22;
        }
      }
      {
        DAST._IExpression _1814_e = _source89.dtor_Print_a0;
        {
          RAST._IExpr _1815_printedExpr;
          DCOMP._IOwnership _1816_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1817_recIdents;
          RAST._IExpr _out202;
          DCOMP._IOwnership _out203;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out204;
          (this).GenExpr(_1814_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out202, out _out203, out _out204);
          _1815_printedExpr = _out202;
          _1816_recOwnership = _out203;
          _1817_recIdents = _out204;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).AsExpr()).Apply1(_1815_printedExpr)));
          readIdents = _1817_recIdents;
          newEnv = env;
        }
      }
    after_match22: ;
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeRangeToRustType(DAST._INewtypeRange range) {
      DAST._INewtypeRange _source95 = range;
      {
        if (_source95.is_NoRange) {
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      {
        if (_source95.is_U8) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      {
        if (_source95.is_U16) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      {
        if (_source95.is_U32) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      {
        if (_source95.is_U64) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      {
        if (_source95.is_U128) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      {
        if (_source95.is_I8) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      {
        if (_source95.is_I16) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      {
        if (_source95.is_I32) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      {
        if (_source95.is_I64) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      {
        if (_source95.is_I128) {
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      {
        return Std.Wrappers.Option<RAST._IType>.create_None();
      }
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
      {
        if (_source96.is_Literal) {
          DAST._ILiteral _h170 = _source96.dtor_Literal_a0;
          if (_h170.is_BoolLiteral) {
            bool _1818_b = _h170.dtor_BoolLiteral_a0;
            {
              RAST._IExpr _out209;
              DCOMP._IOwnership _out210;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1818_b), expectedOwnership, out _out209, out _out210);
              r = _out209;
              resultingOwnership = _out210;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match28;
          }
        }
      }
      {
        if (_source96.is_Literal) {
          DAST._ILiteral _h171 = _source96.dtor_Literal_a0;
          if (_h171.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1819_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1820_t = _h171.dtor_IntLiteral_a1;
            {
              DAST._IType _source97 = _1820_t;
              {
                if (_source97.is_Primitive) {
                  DAST._IPrimitive _h70 = _source97.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    {
                      if ((new BigInteger((_1819_i).Count)) <= (new BigInteger(4))) {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralInt(_1819_i));
                      } else {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1819_i, true, false));
                      }
                    }
                    goto after_match29;
                  }
                }
              }
              {
                DAST._IType _1821_o = _source97;
                {
                  RAST._IType _1822_genType;
                  RAST._IType _out211;
                  _out211 = (this).GenType(_1821_o, DCOMP.GenTypeContext.@default());
                  _1822_genType = _out211;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1819_i), _1822_genType);
                }
              }
            after_match29: ;
              RAST._IExpr _out212;
              DCOMP._IOwnership _out213;
              (this).FromOwned(r, expectedOwnership, out _out212, out _out213);
              r = _out212;
              resultingOwnership = _out213;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match28;
          }
        }
      }
      {
        if (_source96.is_Literal) {
          DAST._ILiteral _h172 = _source96.dtor_Literal_a0;
          if (_h172.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1823_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1824_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1825_t = _h172.dtor_DecLiteral_a2;
            {
              DAST._IType _source98 = _1825_t;
              {
                if (_source98.is_Primitive) {
                  DAST._IPrimitive _h71 = _source98.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1823_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1824_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                    goto after_match30;
                  }
                }
              }
              {
                DAST._IType _1826_o = _source98;
                {
                  RAST._IType _1827_genType;
                  RAST._IType _out214;
                  _out214 = (this).GenType(_1826_o, DCOMP.GenTypeContext.@default());
                  _1827_genType = _out214;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1823_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1824_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1827_genType);
                }
              }
            after_match30: ;
              RAST._IExpr _out215;
              DCOMP._IOwnership _out216;
              (this).FromOwned(r, expectedOwnership, out _out215, out _out216);
              r = _out215;
              resultingOwnership = _out216;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match28;
          }
        }
      }
      {
        if (_source96.is_Literal) {
          DAST._ILiteral _h173 = _source96.dtor_Literal_a0;
          if (_h173.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1828_l = _h173.dtor_StringLiteral_a0;
            bool _1829_verbatim = _h173.dtor_verbatim;
            {
              r = (((RAST.__default.dafny__runtime).MSel((this).string__of)).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1828_l, false, _1829_verbatim));
              RAST._IExpr _out217;
              DCOMP._IOwnership _out218;
              (this).FromOwned(r, expectedOwnership, out _out217, out _out218);
              r = _out217;
              resultingOwnership = _out218;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
            goto after_match28;
          }
        }
      }
      {
        if (_source96.is_Literal) {
          DAST._ILiteral _h174 = _source96.dtor_Literal_a0;
          if (_h174.is_CharLiteralUTF16) {
            BigInteger _1830_c = _h174.dtor_CharLiteralUTF16_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1830_c));
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
            goto after_match28;
          }
        }
      }
      {
        if (_source96.is_Literal) {
          DAST._ILiteral _h175 = _source96.dtor_Literal_a0;
          if (_h175.is_CharLiteral) {
            Dafny.Rune _1831_c = _h175.dtor_CharLiteral_a0;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1831_c).Value)));
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
            goto after_match28;
          }
        }
      }
      {
        DAST._ILiteral _h176 = _source96.dtor_Literal_a0;
        DAST._IType _1832_tpe = _h176.dtor_Null_a0;
        {
          RAST._IType _1833_tpeGen;
          RAST._IType _out223;
          _out223 = (this).GenType(_1832_tpe, DCOMP.GenTypeContext.@default());
          _1833_tpeGen = _out223;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null_mut"));
          } else {
            r = RAST.Expr.create_TypeAscription((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1833_tpeGen);
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
    after_match28: ;
    }
    public void GenExprBinary(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs56 = e;
      DAST._IBinOp _1834_op = _let_tmp_rhs56.dtor_op;
      DAST._IExpression _1835_lExpr = _let_tmp_rhs56.dtor_left;
      DAST._IExpression _1836_rExpr = _let_tmp_rhs56.dtor_right;
      DAST.Format._IBinaryOpFormat _1837_format = _let_tmp_rhs56.dtor_format2;
      bool _1838_becomesLeftCallsRight;
      DAST._IBinOp _source99 = _1834_op;
      {
        bool disjunctiveMatch13 = false;
        if (_source99.is_SetMerge) {
          disjunctiveMatch13 = true;
        }
        if (_source99.is_SetSubtraction) {
          disjunctiveMatch13 = true;
        }
        if (_source99.is_SetIntersection) {
          disjunctiveMatch13 = true;
        }
        if (_source99.is_SetDisjoint) {
          disjunctiveMatch13 = true;
        }
        if (_source99.is_MapMerge) {
          disjunctiveMatch13 = true;
        }
        if (_source99.is_MapSubtraction) {
          disjunctiveMatch13 = true;
        }
        if (_source99.is_MultisetMerge) {
          disjunctiveMatch13 = true;
        }
        if (_source99.is_MultisetSubtraction) {
          disjunctiveMatch13 = true;
        }
        if (_source99.is_MultisetIntersection) {
          disjunctiveMatch13 = true;
        }
        if (_source99.is_MultisetDisjoint) {
          disjunctiveMatch13 = true;
        }
        if (_source99.is_Concat) {
          disjunctiveMatch13 = true;
        }
        if (disjunctiveMatch13) {
          _1838_becomesLeftCallsRight = true;
          goto after_match31;
        }
      }
      {
        _1838_becomesLeftCallsRight = false;
      }
    after_match31: ;
      bool _1839_becomesRightCallsLeft;
      DAST._IBinOp _source100 = _1834_op;
      {
        if (_source100.is_In) {
          _1839_becomesRightCallsLeft = true;
          goto after_match32;
        }
      }
      {
        _1839_becomesRightCallsLeft = false;
      }
    after_match32: ;
      bool _1840_becomesCallLeftRight;
      DAST._IBinOp _source101 = _1834_op;
      {
        if (_source101.is_Eq) {
          bool referential0 = _source101.dtor_referential;
          if ((referential0) == (true)) {
            _1840_becomesCallLeftRight = false;
            goto after_match33;
          }
        }
      }
      {
        if (_source101.is_SetMerge) {
          _1840_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source101.is_SetSubtraction) {
          _1840_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source101.is_SetIntersection) {
          _1840_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source101.is_SetDisjoint) {
          _1840_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source101.is_MapMerge) {
          _1840_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source101.is_MapSubtraction) {
          _1840_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source101.is_MultisetMerge) {
          _1840_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source101.is_MultisetSubtraction) {
          _1840_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source101.is_MultisetIntersection) {
          _1840_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source101.is_MultisetDisjoint) {
          _1840_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        if (_source101.is_Concat) {
          _1840_becomesCallLeftRight = true;
          goto after_match33;
        }
      }
      {
        _1840_becomesCallLeftRight = false;
      }
    after_match33: ;
      DCOMP._IOwnership _1841_expectedLeftOwnership;
      if (_1838_becomesLeftCallsRight) {
        _1841_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else if ((_1839_becomesRightCallsLeft) || (_1840_becomesCallLeftRight)) {
        _1841_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        _1841_expectedLeftOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      DCOMP._IOwnership _1842_expectedRightOwnership;
      if ((_1838_becomesLeftCallsRight) || (_1840_becomesCallLeftRight)) {
        _1842_expectedRightOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else if (_1839_becomesRightCallsLeft) {
        _1842_expectedRightOwnership = DCOMP.Ownership.create_OwnershipAutoBorrowed();
      } else {
        _1842_expectedRightOwnership = DCOMP.Ownership.create_OwnershipOwned();
      }
      RAST._IExpr _1843_left;
      DCOMP._IOwnership _1844___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1845_recIdentsL;
      RAST._IExpr _out226;
      DCOMP._IOwnership _out227;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
      (this).GenExpr(_1835_lExpr, selfIdent, env, _1841_expectedLeftOwnership, out _out226, out _out227, out _out228);
      _1843_left = _out226;
      _1844___v113 = _out227;
      _1845_recIdentsL = _out228;
      RAST._IExpr _1846_right;
      DCOMP._IOwnership _1847___v114;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1848_recIdentsR;
      RAST._IExpr _out229;
      DCOMP._IOwnership _out230;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out231;
      (this).GenExpr(_1836_rExpr, selfIdent, env, _1842_expectedRightOwnership, out _out229, out _out230, out _out231);
      _1846_right = _out229;
      _1847___v114 = _out230;
      _1848_recIdentsR = _out231;
      DAST._IBinOp _source102 = _1834_op;
      {
        if (_source102.is_In) {
          {
            r = ((_1846_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1843_left);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_SeqProperPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1843_left, _1846_right, _1837_format);
          goto after_match34;
        }
      }
      {
        if (_source102.is_SeqPrefix) {
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1843_left, _1846_right, _1837_format);
          goto after_match34;
        }
      }
      {
        if (_source102.is_SetMerge) {
          {
            r = ((_1843_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1846_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_SetSubtraction) {
          {
            r = ((_1843_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1846_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_SetIntersection) {
          {
            r = ((_1843_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1846_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_Subset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1843_left, _1846_right, _1837_format);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_ProperSubset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1843_left, _1846_right, _1837_format);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_SetDisjoint) {
          {
            r = ((_1843_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1846_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_MapMerge) {
          {
            r = ((_1843_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1846_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_MapSubtraction) {
          {
            r = ((_1843_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1846_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_MultisetMerge) {
          {
            r = ((_1843_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1846_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_MultisetSubtraction) {
          {
            r = ((_1843_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1846_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_MultisetIntersection) {
          {
            r = ((_1843_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1846_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_Submultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1843_left, _1846_right, _1837_format);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_ProperSubmultiset) {
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1843_left, _1846_right, _1837_format);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_MultisetDisjoint) {
          {
            r = ((_1843_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1846_right);
          }
          goto after_match34;
        }
      }
      {
        if (_source102.is_Concat) {
          {
            r = ((_1843_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1846_right);
          }
          goto after_match34;
        }
      }
      {
        {
          if ((DCOMP.COMP.OpTable).Contains(_1834_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1834_op), _1843_left, _1846_right, _1837_format);
          } else {
            DAST._IBinOp _source103 = _1834_op;
            {
              if (_source103.is_Eq) {
                bool _1849_referential = _source103.dtor_referential;
                {
                  if (_1849_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1843_left, _1846_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1836_rExpr).is_SeqValue) && ((new BigInteger(((_1836_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1843_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1835_lExpr).is_SeqValue) && ((new BigInteger(((_1835_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1846_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1843_left, _1846_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
                goto after_match35;
              }
            }
            {
              if (_source103.is_EuclidianDiv) {
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1843_left, _1846_right));
                }
                goto after_match35;
              }
            }
            {
              if (_source103.is_EuclidianMod) {
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1843_left, _1846_right));
                }
                goto after_match35;
              }
            }
            {
              Dafny.ISequence<Dafny.Rune> _1850_op = _source103.dtor_Passthrough_a0;
              {
                r = RAST.Expr.create_BinaryOp(_1850_op, _1843_left, _1846_right, _1837_format);
              }
            }
          after_match35: ;
          }
        }
      }
    after_match34: ;
      RAST._IExpr _out232;
      DCOMP._IOwnership _out233;
      (this).FromOwned(r, expectedOwnership, out _out232, out _out233);
      r = _out232;
      resultingOwnership = _out233;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1845_recIdentsL, _1848_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs57 = e;
      DAST._IExpression _1851_expr = _let_tmp_rhs57.dtor_value;
      DAST._IType _1852_fromTpe = _let_tmp_rhs57.dtor_from;
      DAST._IType _1853_toTpe = _let_tmp_rhs57.dtor_typ;
      DAST._IType _let_tmp_rhs58 = _1853_toTpe;
      DAST._IResolvedType _let_tmp_rhs59 = _let_tmp_rhs58.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1854_path = _let_tmp_rhs59.dtor_path;
      Dafny.ISequence<DAST._IType> _1855_typeArgs = _let_tmp_rhs59.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs60 = _let_tmp_rhs59.dtor_kind;
      DAST._IType _1856_b = _let_tmp_rhs60.dtor_baseType;
      DAST._INewtypeRange _1857_range = _let_tmp_rhs60.dtor_range;
      bool _1858_erase = _let_tmp_rhs60.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1859___v116 = _let_tmp_rhs59.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1860___v117 = _let_tmp_rhs59.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1861___v118 = _let_tmp_rhs59.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1862_nativeToType;
      _1862_nativeToType = DCOMP.COMP.NewtypeRangeToRustType(_1857_range);
      if (object.Equals(_1852_fromTpe, _1856_b)) {
        RAST._IExpr _1863_recursiveGen;
        DCOMP._IOwnership _1864_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1865_recIdents;
        RAST._IExpr _out234;
        DCOMP._IOwnership _out235;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out236;
        (this).GenExpr(_1851_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out234, out _out235, out _out236);
        _1863_recursiveGen = _out234;
        _1864_recOwned = _out235;
        _1865_recIdents = _out236;
        readIdents = _1865_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source104 = _1862_nativeToType;
        {
          if (_source104.is_Some) {
            RAST._IType _1866_v = _source104.dtor_value;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1863_recursiveGen, RAST.Expr.create_ExprFromType(_1866_v)));
            RAST._IExpr _out237;
            DCOMP._IOwnership _out238;
            (this).FromOwned(r, expectedOwnership, out _out237, out _out238);
            r = _out237;
            resultingOwnership = _out238;
            goto after_match36;
          }
        }
        {
          if (_1858_erase) {
            r = _1863_recursiveGen;
          } else {
            RAST._IType _1867_rhsType;
            RAST._IType _out239;
            _out239 = (this).GenType(_1853_toTpe, DCOMP.GenTypeContext.@default());
            _1867_rhsType = _out239;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1867_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1863_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out240;
          DCOMP._IOwnership _out241;
          (this).FromOwnership(r, _1864_recOwned, expectedOwnership, out _out240, out _out241);
          r = _out240;
          resultingOwnership = _out241;
        }
      after_match36: ;
      } else {
        if ((_1862_nativeToType).is_Some) {
          DAST._IType _source105 = _1852_fromTpe;
          {
            if (_source105.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source105.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1868_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1869_range0 = kind1.dtor_range;
                bool _1870_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1871_attributes0 = resolved1.dtor_attributes;
                {
                  Std.Wrappers._IOption<RAST._IType> _1872_nativeFromType;
                  _1872_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1869_range0);
                  if ((_1872_nativeFromType).is_Some) {
                    RAST._IExpr _1873_recursiveGen;
                    DCOMP._IOwnership _1874_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1875_recIdents;
                    RAST._IExpr _out242;
                    DCOMP._IOwnership _out243;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out244;
                    (this).GenExpr(_1851_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out242, out _out243, out _out244);
                    _1873_recursiveGen = _out242;
                    _1874_recOwned = _out243;
                    _1875_recIdents = _out244;
                    RAST._IExpr _out245;
                    DCOMP._IOwnership _out246;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1873_recursiveGen, (_1862_nativeToType).dtor_value), _1874_recOwned, expectedOwnership, out _out245, out _out246);
                    r = _out245;
                    resultingOwnership = _out246;
                    readIdents = _1875_recIdents;
                    return ;
                  }
                }
                goto after_match37;
              }
            }
          }
          {
          }
        after_match37: ;
          if (object.Equals(_1852_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1876_recursiveGen;
            DCOMP._IOwnership _1877_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1878_recIdents;
            RAST._IExpr _out247;
            DCOMP._IOwnership _out248;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
            (this).GenExpr(_1851_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out247, out _out248, out _out249);
            _1876_recursiveGen = _out247;
            _1877_recOwned = _out248;
            _1878_recIdents = _out249;
            RAST._IExpr _out250;
            DCOMP._IOwnership _out251;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1876_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1862_nativeToType).dtor_value), _1877_recOwned, expectedOwnership, out _out250, out _out251);
            r = _out250;
            resultingOwnership = _out251;
            readIdents = _1878_recIdents;
            return ;
          }
        }
        RAST._IExpr _out252;
        DCOMP._IOwnership _out253;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out254;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1851_expr, _1852_fromTpe, _1856_b), _1856_b, _1853_toTpe), selfIdent, env, expectedOwnership, out _out252, out _out253, out _out254);
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
      DAST._IExpression _1879_expr = _let_tmp_rhs61.dtor_value;
      DAST._IType _1880_fromTpe = _let_tmp_rhs61.dtor_from;
      DAST._IType _1881_toTpe = _let_tmp_rhs61.dtor_typ;
      DAST._IType _let_tmp_rhs62 = _1880_fromTpe;
      DAST._IResolvedType _let_tmp_rhs63 = _let_tmp_rhs62.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1882___v124 = _let_tmp_rhs63.dtor_path;
      Dafny.ISequence<DAST._IType> _1883___v125 = _let_tmp_rhs63.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs64 = _let_tmp_rhs63.dtor_kind;
      DAST._IType _1884_b = _let_tmp_rhs64.dtor_baseType;
      DAST._INewtypeRange _1885_range = _let_tmp_rhs64.dtor_range;
      bool _1886_erase = _let_tmp_rhs64.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1887_attributes = _let_tmp_rhs63.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1888___v126 = _let_tmp_rhs63.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1889___v127 = _let_tmp_rhs63.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1890_nativeFromType;
      _1890_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1885_range);
      if (object.Equals(_1884_b, _1881_toTpe)) {
        RAST._IExpr _1891_recursiveGen;
        DCOMP._IOwnership _1892_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1893_recIdents;
        RAST._IExpr _out255;
        DCOMP._IOwnership _out256;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out257;
        (this).GenExpr(_1879_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out255, out _out256, out _out257);
        _1891_recursiveGen = _out255;
        _1892_recOwned = _out256;
        _1893_recIdents = _out257;
        readIdents = _1893_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source106 = _1890_nativeFromType;
        {
          if (_source106.is_Some) {
            RAST._IType _1894_v = _source106.dtor_value;
            RAST._IType _1895_toTpeRust;
            RAST._IType _out258;
            _out258 = (this).GenType(_1881_toTpe, DCOMP.GenTypeContext.@default());
            _1895_toTpeRust = _out258;
            r = ((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1895_toTpeRust))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1891_recursiveGen));
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            (this).FromOwned(r, expectedOwnership, out _out259, out _out260);
            r = _out259;
            resultingOwnership = _out260;
            goto after_match38;
          }
        }
        {
          if (_1886_erase) {
            r = _1891_recursiveGen;
          } else {
            r = (_1891_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out261;
          DCOMP._IOwnership _out262;
          (this).FromOwnership(r, _1892_recOwned, expectedOwnership, out _out261, out _out262);
          r = _out261;
          resultingOwnership = _out262;
        }
      after_match38: ;
      } else {
        if ((_1890_nativeFromType).is_Some) {
          if (object.Equals(_1881_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1896_recursiveGen;
            DCOMP._IOwnership _1897_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1898_recIdents;
            RAST._IExpr _out263;
            DCOMP._IOwnership _out264;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out265;
            (this).GenExpr(_1879_expr, selfIdent, env, expectedOwnership, out _out263, out _out264, out _out265);
            _1896_recursiveGen = _out263;
            _1897_recOwned = _out264;
            _1898_recIdents = _out265;
            RAST._IExpr _out266;
            DCOMP._IOwnership _out267;
            (this).FromOwnership((((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(RAST.Expr.create_TypeAscription(_1896_recursiveGen, (this).DafnyCharUnderlying)), _1897_recOwned, expectedOwnership, out _out266, out _out267);
            r = _out266;
            resultingOwnership = _out267;
            readIdents = _1898_recIdents;
            return ;
          }
        }
        RAST._IExpr _out268;
        DCOMP._IOwnership _out269;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out270;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1879_expr, _1880_fromTpe, _1884_b), _1884_b, _1881_toTpe), selfIdent, env, expectedOwnership, out _out268, out _out269, out _out270);
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
        Std.Wrappers._IResult<__T, __E> _1899_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1899_valueOrError0).IsFailure()) {
          return (_1899_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1900_head = (_1899_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1901_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1901_valueOrError1).IsFailure()) {
            return (_1901_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1902_tail = (_1901_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1900_head), _1902_tail));
          }
        }
      }
    }
    public Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> UpcastConversionLambda(DAST._IType fromType, RAST._IType fromTpe, DAST._IType toType, RAST._IType toTpe, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> typeParams)
    {
      var _pat_let_tv4 = fromType;
      var _pat_let_tv5 = fromTpe;
      var _pat_let_tv6 = toType;
      var _pat_let_tv7 = toTpe;
      var _pat_let_tv8 = typeParams;
      if (object.Equals(fromTpe, toTpe)) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("upcast_id"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(fromTpe))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
      } else if (((fromTpe).IsObjectOrPointer()) && ((toTpe).IsObjectOrPointer())) {
        if (!(((toTpe).ObjectOrPointerUnderlying()).is_DynType)) {
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Failure(_System.Tuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>.create(fromType, fromTpe, toType, toTpe, typeParams));
        } else {
          RAST._IType _1903_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1904_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel((this).upcast)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1903_fromTpeUnderlying, _1904_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1905_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1905_valueOrError0).IsFailure()) {
          return (_1905_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1906_lambda = (_1905_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1906_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).AsExpr()).Apply1(_1906_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Dafny.ISequence<BigInteger> _1907_indices = ((((fromType).is_UserDefined) && ((((fromType).dtor_resolved).dtor_kind).is_Datatype)) ? (Std.Collections.Seq.__default.Filter<BigInteger>(Dafny.Helpers.Id<Func<RAST._IType, DAST._IType, Func<BigInteger, bool>>>((_1908_fromTpe, _1909_fromType) => ((System.Func<BigInteger, bool>)((_1910_i) => {
          return ((((_1910_i).Sign != -1) && ((_1910_i) < (new BigInteger(((_1908_fromTpe).dtor_arguments).Count)))) ? (!(((_1910_i).Sign != -1) && ((_1910_i) < (new BigInteger(((((_1909_fromType).dtor_resolved).dtor_kind).dtor_variances).Count)))) || (!((((((_1909_fromType).dtor_resolved).dtor_kind).dtor_variances).Select(_1910_i)).is_Nonvariant))) : (false));
        })))(fromTpe, fromType), ((System.Func<Dafny.ISequence<BigInteger>>) (() => {
          BigInteger dim14 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr14 = new BigInteger[Dafny.Helpers.ToIntChecked(dim14, "array size exceeds memory limit")];
          for (int i14 = 0; i14 < dim14; i14++) {
            var _1911_i = (BigInteger) i14;
            arr14[(int)(_1911_i)] = _1911_i;
          }
          return Dafny.Sequence<BigInteger>.FromArray(arr14);
        }))())) : (((System.Func<Dafny.ISequence<BigInteger>>) (() => {
          BigInteger dim15 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr15 = new BigInteger[Dafny.Helpers.ToIntChecked(dim15, "array size exceeds memory limit")];
          for (int i15 = 0; i15 < dim15; i15++) {
            var _1912_i = (BigInteger) i15;
            arr15[(int)(_1912_i)] = _1912_i;
          }
          return Dafny.Sequence<BigInteger>.FromArray(arr15);
        }))()));
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1913_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim16 = new BigInteger((_1907_indices).Count);
          var arr16 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim16, "array size exceeds memory limit")];
          for (int i16 = 0; i16 < dim16; i16++) {
            var _1914_j = (BigInteger) i16;
            arr16[(int)(_1914_j)] = Dafny.Helpers.Let<BigInteger, Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>((_1907_indices).Select(_1914_j), _pat_let24_0 => Dafny.Helpers.Let<BigInteger, Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>(_pat_let24_0, _1915_i => (this).UpcastConversionLambda((((_pat_let_tv4).dtor_resolved).dtor_typeArgs).Select(_1915_i), ((_pat_let_tv5).dtor_arguments).Select(_1915_i), (((_pat_let_tv6).dtor_resolved).dtor_typeArgs).Select(_1915_i), ((_pat_let_tv7).dtor_arguments).Select(_1915_i), _pat_let_tv8)));
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr16);
        }))());
        if ((_1913_valueOrError1).IsFailure()) {
          return (_1913_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1916_lambdas = (_1913_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim17 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr17 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim17, "array size exceeds memory limit")];
  for (int i17 = 0; i17 < dim17; i17++) {
    var _1917_i = (BigInteger) i17;
    arr17[(int)(_1917_i)] = ((fromTpe).dtor_arguments).Select(_1917_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr17);
}))())).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1916_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1918_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1919_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1920_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1921_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1922_valueOrError2 = (this).UpcastConversionLambda(_1920_newFromType, _1918_newFromTpe, _1921_newToType, _1919_newToTpe, typeParams);
        if ((_1922_valueOrError2).IsFailure()) {
          return (_1922_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1923_coerceArg = (_1922_valueOrError2).Extract();
          RAST._IPath _1924_collectionType = (RAST.__default.dafny__runtime).MSel(((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name);
          RAST._IExpr _1925_baseType = (((((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? (((_1924_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((((fromTpe).Expand()).dtor_arguments).Select(BigInteger.Zero), _1918_newFromTpe))) : (((_1924_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1918_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1925_baseType).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1923_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1926_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1926_valueOrError3).IsFailure()) {
          return (_1926_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1927_lambda = (_1926_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1927_lambda));
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
      DAST._IExpression _1928_expr = _let_tmp_rhs65.dtor_value;
      DAST._IType _1929_fromTpe = _let_tmp_rhs65.dtor_from;
      DAST._IType _1930_toTpe = _let_tmp_rhs65.dtor_typ;
      RAST._IType _1931_fromTpeGen;
      RAST._IType _out271;
      _out271 = (this).GenType(_1929_fromTpe, DCOMP.GenTypeContext.@default());
      _1931_fromTpeGen = _out271;
      RAST._IType _1932_toTpeGen;
      RAST._IType _out272;
      _out272 = (this).GenType(_1930_toTpe, DCOMP.GenTypeContext.@default());
      _1932_toTpeGen = _out272;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1933_upcastConverter;
      _1933_upcastConverter = (this).UpcastConversionLambda(_1929_fromTpe, _1931_fromTpeGen, _1930_toTpe, _1932_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1933_upcastConverter).is_Success) {
        RAST._IExpr _1934_conversionLambda;
        _1934_conversionLambda = (_1933_upcastConverter).dtor_value;
        RAST._IExpr _1935_recursiveGen;
        DCOMP._IOwnership _1936_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1937_recIdents;
        RAST._IExpr _out273;
        DCOMP._IOwnership _out274;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out275;
        (this).GenExpr(_1928_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out273, out _out274, out _out275);
        _1935_recursiveGen = _out273;
        _1936_recOwned = _out274;
        _1937_recIdents = _out275;
        readIdents = _1937_recIdents;
        r = (_1934_conversionLambda).Apply1(_1935_recursiveGen);
        RAST._IExpr _out276;
        DCOMP._IOwnership _out277;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out276, out _out277);
        r = _out276;
        resultingOwnership = _out277;
      } else if ((this).IsDowncastConversion(_1931_fromTpeGen, _1932_toTpeGen)) {
        RAST._IExpr _1938_recursiveGen;
        DCOMP._IOwnership _1939_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1940_recIdents;
        RAST._IExpr _out278;
        DCOMP._IOwnership _out279;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out280;
        (this).GenExpr(_1928_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out278, out _out279, out _out280);
        _1938_recursiveGen = _out278;
        _1939_recOwned = _out279;
        _1940_recIdents = _out280;
        readIdents = _1940_recIdents;
        _1932_toTpeGen = (_1932_toTpeGen).ObjectOrPointerUnderlying();
        r = (((RAST.__default.dafny__runtime).MSel((this).downcast)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1938_recursiveGen, RAST.Expr.create_ExprFromType(_1932_toTpeGen)));
        RAST._IExpr _out281;
        DCOMP._IOwnership _out282;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out281, out _out282);
        r = _out281;
        resultingOwnership = _out282;
      } else {
        RAST._IExpr _1941_recursiveGen;
        DCOMP._IOwnership _1942_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1943_recIdents;
        RAST._IExpr _out283;
        DCOMP._IOwnership _out284;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out285;
        (this).GenExpr(_1928_expr, selfIdent, env, expectedOwnership, out _out283, out _out284, out _out285);
        _1941_recursiveGen = _out283;
        _1942_recOwned = _out284;
        _1943_recIdents = _out285;
        readIdents = _1943_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs66 = _1933_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs67 = _let_tmp_rhs66.dtor_error;
        DAST._IType _1944_fromType = _let_tmp_rhs67.dtor__0;
        RAST._IType _1945_fromTpeGen = _let_tmp_rhs67.dtor__1;
        DAST._IType _1946_toType = _let_tmp_rhs67.dtor__2;
        RAST._IType _1947_toTpeGen = _let_tmp_rhs67.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1948_m = _let_tmp_rhs67.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1949_msg;
        _1949_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1945_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1947_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1949_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1941_recursiveGen)._ToString(DCOMP.__default.IND), _1949_msg));
        RAST._IExpr _out286;
        DCOMP._IOwnership _out287;
        (this).FromOwnership(r, _1942_recOwned, expectedOwnership, out _out286, out _out287);
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
      DAST._IExpression _1950_expr = _let_tmp_rhs68.dtor_value;
      DAST._IType _1951_fromTpe = _let_tmp_rhs68.dtor_from;
      DAST._IType _1952_toTpe = _let_tmp_rhs68.dtor_typ;
      if (object.Equals(_1951_fromTpe, _1952_toTpe)) {
        RAST._IExpr _1953_recursiveGen;
        DCOMP._IOwnership _1954_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1955_recIdents;
        RAST._IExpr _out288;
        DCOMP._IOwnership _out289;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out290;
        (this).GenExpr(_1950_expr, selfIdent, env, expectedOwnership, out _out288, out _out289, out _out290);
        _1953_recursiveGen = _out288;
        _1954_recOwned = _out289;
        _1955_recIdents = _out290;
        r = _1953_recursiveGen;
        RAST._IExpr _out291;
        DCOMP._IOwnership _out292;
        (this).FromOwnership(r, _1954_recOwned, expectedOwnership, out _out291, out _out292);
        r = _out291;
        resultingOwnership = _out292;
        readIdents = _1955_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source107 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1951_fromTpe, _1952_toTpe);
        {
          DAST._IType _10 = _source107.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1956_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1957_range = kind2.dtor_range;
              bool _1958_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1959_attributes = resolved2.dtor_attributes;
              {
                RAST._IExpr _out293;
                DCOMP._IOwnership _out294;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out295;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out293, out _out294, out _out295);
                r = _out293;
                resultingOwnership = _out294;
                readIdents = _out295;
              }
              goto after_match39;
            }
          }
        }
        {
          DAST._IType _00 = _source107.dtor__0;
          if (_00.is_UserDefined) {
            DAST._IResolvedType resolved3 = _00.dtor_resolved;
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1960_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1961_range = kind3.dtor_range;
              bool _1962_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1963_attributes = resolved3.dtor_attributes;
              {
                RAST._IExpr _out296;
                DCOMP._IOwnership _out297;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out296, out _out297, out _out298);
                r = _out296;
                resultingOwnership = _out297;
                readIdents = _out298;
              }
              goto after_match39;
            }
          }
        }
        {
          DAST._IType _01 = _source107.dtor__0;
          if (_01.is_Primitive) {
            DAST._IPrimitive _h72 = _01.dtor_Primitive_a0;
            if (_h72.is_Int) {
              DAST._IType _11 = _source107.dtor__1;
              if (_11.is_Primitive) {
                DAST._IPrimitive _h73 = _11.dtor_Primitive_a0;
                if (_h73.is_Real) {
                  {
                    RAST._IExpr _1964_recursiveGen;
                    DCOMP._IOwnership _1965___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1966_recIdents;
                    RAST._IExpr _out299;
                    DCOMP._IOwnership _out300;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out301;
                    (this).GenExpr(_1950_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out299, out _out300, out _out301);
                    _1964_recursiveGen = _out299;
                    _1965___v138 = _out300;
                    _1966_recIdents = _out301;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1964_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out302;
                    DCOMP._IOwnership _out303;
                    (this).FromOwned(r, expectedOwnership, out _out302, out _out303);
                    r = _out302;
                    resultingOwnership = _out303;
                    readIdents = _1966_recIdents;
                  }
                  goto after_match39;
                }
              }
            }
          }
        }
        {
          DAST._IType _02 = _source107.dtor__0;
          if (_02.is_Primitive) {
            DAST._IPrimitive _h74 = _02.dtor_Primitive_a0;
            if (_h74.is_Real) {
              DAST._IType _12 = _source107.dtor__1;
              if (_12.is_Primitive) {
                DAST._IPrimitive _h75 = _12.dtor_Primitive_a0;
                if (_h75.is_Int) {
                  {
                    RAST._IExpr _1967_recursiveGen;
                    DCOMP._IOwnership _1968___v139;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1969_recIdents;
                    RAST._IExpr _out304;
                    DCOMP._IOwnership _out305;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out306;
                    (this).GenExpr(_1950_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out304, out _out305, out _out306);
                    _1967_recursiveGen = _out304;
                    _1968___v139 = _out305;
                    _1969_recIdents = _out306;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1967_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out307;
                    DCOMP._IOwnership _out308;
                    (this).FromOwned(r, expectedOwnership, out _out307, out _out308);
                    r = _out307;
                    resultingOwnership = _out308;
                    readIdents = _1969_recIdents;
                  }
                  goto after_match39;
                }
              }
            }
          }
        }
        {
          DAST._IType _03 = _source107.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h76 = _03.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _13 = _source107.dtor__1;
              if (_13.is_Passthrough) {
                {
                  RAST._IType _1970_rhsType;
                  RAST._IType _out309;
                  _out309 = (this).GenType(_1952_toTpe, DCOMP.GenTypeContext.@default());
                  _1970_rhsType = _out309;
                  RAST._IExpr _1971_recursiveGen;
                  DCOMP._IOwnership _1972___v141;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1973_recIdents;
                  RAST._IExpr _out310;
                  DCOMP._IOwnership _out311;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out312;
                  (this).GenExpr(_1950_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out310, out _out311, out _out312);
                  _1971_recursiveGen = _out310;
                  _1972___v141 = _out311;
                  _1973_recIdents = _out312;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1970_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1971_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out313;
                  DCOMP._IOwnership _out314;
                  (this).FromOwned(r, expectedOwnership, out _out313, out _out314);
                  r = _out313;
                  resultingOwnership = _out314;
                  readIdents = _1973_recIdents;
                }
                goto after_match39;
              }
            }
          }
        }
        {
          DAST._IType _04 = _source107.dtor__0;
          if (_04.is_Passthrough) {
            DAST._IType _14 = _source107.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h77 = _14.dtor_Primitive_a0;
              if (_h77.is_Int) {
                {
                  RAST._IType _1974_rhsType;
                  RAST._IType _out315;
                  _out315 = (this).GenType(_1951_fromTpe, DCOMP.GenTypeContext.@default());
                  _1974_rhsType = _out315;
                  RAST._IExpr _1975_recursiveGen;
                  DCOMP._IOwnership _1976___v143;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1977_recIdents;
                  RAST._IExpr _out316;
                  DCOMP._IOwnership _out317;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out318;
                  (this).GenExpr(_1950_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out316, out _out317, out _out318);
                  _1975_recursiveGen = _out316;
                  _1976___v143 = _out317;
                  _1977_recIdents = _out318;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1975_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out319;
                  DCOMP._IOwnership _out320;
                  (this).FromOwned(r, expectedOwnership, out _out319, out _out320);
                  r = _out319;
                  resultingOwnership = _out320;
                  readIdents = _1977_recIdents;
                }
                goto after_match39;
              }
            }
          }
        }
        {
          DAST._IType _05 = _source107.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h78 = _05.dtor_Primitive_a0;
            if (_h78.is_Int) {
              DAST._IType _15 = _source107.dtor__1;
              if (_15.is_Primitive) {
                DAST._IPrimitive _h79 = _15.dtor_Primitive_a0;
                if (_h79.is_Char) {
                  {
                    RAST._IType _1978_rhsType;
                    RAST._IType _out321;
                    _out321 = (this).GenType(_1952_toTpe, DCOMP.GenTypeContext.@default());
                    _1978_rhsType = _out321;
                    RAST._IExpr _1979_recursiveGen;
                    DCOMP._IOwnership _1980___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1981_recIdents;
                    RAST._IExpr _out322;
                    DCOMP._IOwnership _out323;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out324;
                    (this).GenExpr(_1950_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out322, out _out323, out _out324);
                    _1979_recursiveGen = _out322;
                    _1980___v144 = _out323;
                    _1981_recIdents = _out324;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1979_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out325;
                    DCOMP._IOwnership _out326;
                    (this).FromOwned(r, expectedOwnership, out _out325, out _out326);
                    r = _out325;
                    resultingOwnership = _out326;
                    readIdents = _1981_recIdents;
                  }
                  goto after_match39;
                }
              }
            }
          }
        }
        {
          DAST._IType _06 = _source107.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h710 = _06.dtor_Primitive_a0;
            if (_h710.is_Char) {
              DAST._IType _16 = _source107.dtor__1;
              if (_16.is_Primitive) {
                DAST._IPrimitive _h711 = _16.dtor_Primitive_a0;
                if (_h711.is_Int) {
                  {
                    RAST._IType _1982_rhsType;
                    RAST._IType _out327;
                    _out327 = (this).GenType(_1951_fromTpe, DCOMP.GenTypeContext.@default());
                    _1982_rhsType = _out327;
                    RAST._IExpr _1983_recursiveGen;
                    DCOMP._IOwnership _1984___v145;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1985_recIdents;
                    RAST._IExpr _out328;
                    DCOMP._IOwnership _out329;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out330;
                    (this).GenExpr(_1950_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out328, out _out329, out _out330);
                    _1983_recursiveGen = _out328;
                    _1984___v145 = _out329;
                    _1985_recIdents = _out330;
                    r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1((_1983_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out331;
                    DCOMP._IOwnership _out332;
                    (this).FromOwned(r, expectedOwnership, out _out331, out _out332);
                    r = _out331;
                    resultingOwnership = _out332;
                    readIdents = _1985_recIdents;
                  }
                  goto after_match39;
                }
              }
            }
          }
        }
        {
          DAST._IType _07 = _source107.dtor__0;
          if (_07.is_Passthrough) {
            DAST._IType _17 = _source107.dtor__1;
            if (_17.is_Passthrough) {
              {
                RAST._IExpr _1986_recursiveGen;
                DCOMP._IOwnership _1987___v148;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1988_recIdents;
                RAST._IExpr _out333;
                DCOMP._IOwnership _out334;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out335;
                (this).GenExpr(_1950_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out333, out _out334, out _out335);
                _1986_recursiveGen = _out333;
                _1987___v148 = _out334;
                _1988_recIdents = _out335;
                RAST._IType _1989_toTpeGen;
                RAST._IType _out336;
                _out336 = (this).GenType(_1952_toTpe, DCOMP.GenTypeContext.@default());
                _1989_toTpeGen = _out336;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1986_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1989_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out337;
                DCOMP._IOwnership _out338;
                (this).FromOwned(r, expectedOwnership, out _out337, out _out338);
                r = _out337;
                resultingOwnership = _out338;
                readIdents = _1988_recIdents;
              }
              goto after_match39;
            }
          }
        }
        {
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
      after_match39: ;
      }
      return ;
    }
    public void GenIdent(Dafny.ISequence<Dafny.Rune> rName, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      r = RAST.Expr.create_Identifier(rName);
      Std.Wrappers._IOption<RAST._IType> _1990_tpe;
      _1990_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1991_placeboOpt;
      if ((_1990_tpe).is_Some) {
        _1991_placeboOpt = ((_1990_tpe).dtor_value).ExtractMaybePlacebo();
      } else {
        _1991_placeboOpt = Std.Wrappers.Option<RAST._IType>.create_None();
      }
      bool _1992_currentlyBorrowed;
      _1992_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1993_noNeedOfClone;
      _1993_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1991_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1992_currentlyBorrowed = false;
        _1993_noNeedOfClone = true;
        _1990_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1991_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        if (_1992_currentlyBorrowed) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        } else {
          resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
        }
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1990_tpe).is_Some) && (((_1990_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1994_needObjectFromRef;
        _1994_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source108 = (selfIdent).dtor_dafnyType;
          {
            if (_source108.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source108.dtor_resolved;
              DAST._IResolvedTypeBase _1995_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1996_attributes = resolved4.dtor_attributes;
              return ((_1995_base).is_Class) || ((_1995_base).is_Trait);
            }
          }
          {
            return false;
          }
        }))());
        if (_1994_needObjectFromRef) {
          r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1993_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1993_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1992_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1990_tpe).is_Some) && (((_1990_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1997_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1997_attributes).UniqueElements, false, (((_exists_var_2) => {
        DAST._IAttribute _1998_attribute = (DAST._IAttribute)_exists_var_2;
        return ((_1997_attributes).Contains(_1998_attribute)) && ((((_1998_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1998_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      Dafny.ISequence<DAST._IFormal> _1999_signature;
      if ((name).is_CallName) {
        if ((((name).dtor_receiverArg).is_Some) && ((name).dtor_receiverAsArgument)) {
          _1999_signature = Dafny.Sequence<DAST._IFormal>.Concat(Dafny.Sequence<DAST._IFormal>.FromElements(((name).dtor_receiverArg).dtor_value), ((name).dtor_signature));
        } else {
          _1999_signature = ((name).dtor_signature);
        }
      } else {
        _1999_signature = Dafny.Sequence<DAST._IFormal>.FromElements();
      }
      BigInteger _hi38 = new BigInteger((args).Count);
      for (BigInteger _2000_i = BigInteger.Zero; _2000_i < _hi38; _2000_i++) {
        DCOMP._IOwnership _2001_argOwnership;
        _2001_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if ((_2000_i) < (new BigInteger((_1999_signature).Count))) {
          RAST._IType _2002_tpe;
          RAST._IType _out342;
          _out342 = (this).GenType(((_1999_signature).Select(_2000_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _2002_tpe = _out342;
          if ((_2002_tpe).CanReadWithoutClone()) {
            _2001_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _2003_argExpr;
        DCOMP._IOwnership _2004___v155;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2005_argIdents;
        RAST._IExpr _out343;
        DCOMP._IOwnership _out344;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out345;
        (this).GenExpr((args).Select(_2000_i), selfIdent, env, _2001_argOwnership, out _out343, out _out344, out _out345);
        _2003_argExpr = _out343;
        _2004___v155 = _out344;
        _2005_argIdents = _out345;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2003_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2005_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi39 = new BigInteger((typeArgs).Count);
      for (BigInteger _2006_typeI = BigInteger.Zero; _2006_typeI < _hi39; _2006_typeI++) {
        RAST._IType _2007_typeExpr;
        RAST._IType _out346;
        _out346 = (this).GenType((typeArgs).Select(_2006_typeI), DCOMP.GenTypeContext.@default());
        _2007_typeExpr = _out346;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2007_typeExpr));
      }
      DAST._ICallName _source109 = name;
      {
        if (_source109.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _2008_nameIdent = _source109.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType1 = _source109.dtor_onType;
          if (onType1.is_Some) {
            DAST._IType value10 = onType1.dtor_value;
            if (value10.is_UserDefined) {
              DAST._IResolvedType _2009_resolvedType = value10.dtor_resolved;
              if ((((_2009_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_2010_resolvedType, _2011_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.SingleValue<Dafny.ISequence<Dafny.Rune>>(_2011_nameIdent), true, (((_forall_var_8) => {
                Dafny.ISequence<Dafny.Rune> _2012_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                return !(((_2010_resolvedType).dtor_properMethods).Contains(_2012_m)) || (!object.Equals(_2012_m, _2011_nameIdent));
              }))))(_2009_resolvedType, _2008_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_2009_resolvedType, (_2008_nameIdent)), _2009_resolvedType));
              } else {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
              }
              goto after_match40;
            }
          }
        }
      }
      {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    after_match40: ;
      if ((((((fullNameQualifier).is_Some) && ((selfIdent).is_ThisTyped)) && (((selfIdent).dtor_dafnyType).is_UserDefined)) && ((this).IsSameResolvedType(((selfIdent).dtor_dafnyType).dtor_resolved, (fullNameQualifier).dtor_value))) && (!((this).HasExternAttributeRenamingModule(((fullNameQualifier).dtor_value).dtor_attributes)))) {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    }
    public Dafny.ISequence<Dafny.Rune> GetMethodName(DAST._IExpression @on, DAST._ICallName name)
    {
      DAST._ICallName _source110 = name;
      {
        if (_source110.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _2013_ident = _source110.dtor_name;
          if ((@on).is_ExternCompanion) {
            return (_2013_ident);
          } else {
            return DCOMP.__default.escapeName(_2013_ident);
          }
        }
      }
      {
        bool disjunctiveMatch14 = false;
        if (_source110.is_MapBuilderAdd) {
          disjunctiveMatch14 = true;
        }
        if (_source110.is_SetBuilderAdd) {
          disjunctiveMatch14 = true;
        }
        if (disjunctiveMatch14) {
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
        }
      }
      {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
      }
    }
    public void GenExpr(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source111 = e;
      {
        if (_source111.is_Literal) {
          RAST._IExpr _out347;
          DCOMP._IOwnership _out348;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out347, out _out348, out _out349);
          r = _out347;
          resultingOwnership = _out348;
          readIdents = _out349;
          goto after_match41;
        }
      }
      {
        if (_source111.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _2014_name = _source111.dtor_name;
          {
            RAST._IExpr _out350;
            DCOMP._IOwnership _out351;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out352;
            (this).GenIdent(DCOMP.__default.escapeVar(_2014_name), selfIdent, env, expectedOwnership, out _out350, out _out351, out _out352);
            r = _out350;
            resultingOwnership = _out351;
            readIdents = _out352;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_ExternCompanion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2015_path = _source111.dtor_ExternCompanion_a0;
          {
            RAST._IExpr _out353;
            _out353 = DCOMP.COMP.GenPathExpr(_2015_path, false);
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
          goto after_match41;
        }
      }
      {
        if (_source111.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2016_path = _source111.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _2017_typeArgs = _source111.dtor_typeArgs;
          {
            RAST._IExpr _out356;
            _out356 = DCOMP.COMP.GenPathExpr(_2016_path, true);
            r = _out356;
            if ((new BigInteger((_2017_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _2018_typeExprs;
              _2018_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_2017_typeArgs).Count);
              for (BigInteger _2019_i = BigInteger.Zero; _2019_i < _hi40; _2019_i++) {
                RAST._IType _2020_typeExpr;
                RAST._IType _out357;
                _out357 = (this).GenType((_2017_typeArgs).Select(_2019_i), DCOMP.GenTypeContext.@default());
                _2020_typeExpr = _out357;
                _2018_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_2018_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2020_typeExpr));
              }
              r = (r).ApplyType(_2018_typeExprs);
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
          goto after_match41;
        }
      }
      {
        if (_source111.is_InitializationValue) {
          DAST._IType _2021_typ = _source111.dtor_typ;
          {
            RAST._IType _2022_typExpr;
            RAST._IType _out360;
            _out360 = (this).GenType(_2021_typ, DCOMP.GenTypeContext.@default());
            _2022_typExpr = _out360;
            if ((_2022_typExpr).IsObjectOrPointer()) {
              r = (_2022_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_2022_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            }
            RAST._IExpr _out361;
            DCOMP._IOwnership _out362;
            (this).FromOwned(r, expectedOwnership, out _out361, out _out362);
            r = _out361;
            resultingOwnership = _out362;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _2023_values = _source111.dtor_Tuple_a0;
          {
            Dafny.ISequence<RAST._IExpr> _2024_exprs;
            _2024_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi41 = new BigInteger((_2023_values).Count);
            for (BigInteger _2025_i = BigInteger.Zero; _2025_i < _hi41; _2025_i++) {
              RAST._IExpr _2026_recursiveGen;
              DCOMP._IOwnership _2027___v165;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2028_recIdents;
              RAST._IExpr _out363;
              DCOMP._IOwnership _out364;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out365;
              (this).GenExpr((_2023_values).Select(_2025_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out363, out _out364, out _out365);
              _2026_recursiveGen = _out363;
              _2027___v165 = _out364;
              _2028_recIdents = _out365;
              _2024_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_2024_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_2026_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2028_recIdents);
            }
            if ((new BigInteger((_2023_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) {
              r = RAST.Expr.create_Tuple(_2024_exprs);
            } else {
              r = RAST.__default.SystemTuple(_2024_exprs);
            }
            RAST._IExpr _out366;
            DCOMP._IOwnership _out367;
            (this).FromOwned(r, expectedOwnership, out _out366, out _out367);
            r = _out366;
            resultingOwnership = _out367;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2029_path = _source111.dtor_path;
          Dafny.ISequence<DAST._IType> _2030_typeArgs = _source111.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2031_args = _source111.dtor_args;
          {
            RAST._IExpr _out368;
            _out368 = DCOMP.COMP.GenPathExpr(_2029_path, true);
            r = _out368;
            if ((new BigInteger((_2030_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _2032_typeExprs;
              _2032_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi42 = new BigInteger((_2030_typeArgs).Count);
              for (BigInteger _2033_i = BigInteger.Zero; _2033_i < _hi42; _2033_i++) {
                RAST._IType _2034_typeExpr;
                RAST._IType _out369;
                _out369 = (this).GenType((_2030_typeArgs).Select(_2033_i), DCOMP.GenTypeContext.@default());
                _2034_typeExpr = _out369;
                _2032_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_2032_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_2034_typeExpr));
              }
              r = (r).ApplyType(_2032_typeExprs);
            }
            r = (r).FSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _2035_arguments;
            _2035_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi43 = new BigInteger((_2031_args).Count);
            for (BigInteger _2036_i = BigInteger.Zero; _2036_i < _hi43; _2036_i++) {
              RAST._IExpr _2037_recursiveGen;
              DCOMP._IOwnership _2038___v166;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2039_recIdents;
              RAST._IExpr _out370;
              DCOMP._IOwnership _out371;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out372;
              (this).GenExpr((_2031_args).Select(_2036_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out370, out _out371, out _out372);
              _2037_recursiveGen = _out370;
              _2038___v166 = _out371;
              _2039_recIdents = _out372;
              _2035_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2035_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2037_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2039_recIdents);
            }
            r = (r).Apply(_2035_arguments);
            RAST._IExpr _out373;
            DCOMP._IOwnership _out374;
            (this).FromOwned(r, expectedOwnership, out _out373, out _out374);
            r = _out373;
            resultingOwnership = _out374;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _2040_dims = _source111.dtor_dims;
          DAST._IType _2041_typ = _source111.dtor_typ;
          {
            if ((new BigInteger(16)) < (new BigInteger((_2040_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _2042_msg;
              _2042_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2042_msg);
              }
              r = RAST.Expr.create_RawExpr(_2042_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _2043_typeGen;
              RAST._IType _out375;
              _out375 = (this).GenType(_2041_typ, DCOMP.GenTypeContext.@default());
              _2043_typeGen = _out375;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _2044_dimExprs;
              _2044_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi44 = new BigInteger((_2040_dims).Count);
              for (BigInteger _2045_i = BigInteger.Zero; _2045_i < _hi44; _2045_i++) {
                RAST._IExpr _2046_recursiveGen;
                DCOMP._IOwnership _2047___v167;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2048_recIdents;
                RAST._IExpr _out376;
                DCOMP._IOwnership _out377;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out378;
                (this).GenExpr((_2040_dims).Select(_2045_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out376, out _out377, out _out378);
                _2046_recursiveGen = _out376;
                _2047___v167 = _out377;
                _2048_recIdents = _out378;
                _2044_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_2044_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_2046_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2048_recIdents);
              }
              if ((new BigInteger((_2040_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _2049_class__name;
                _2049_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_2040_dims).Count)));
                r = (((((RAST.__default.dafny__runtime).MSel(_2049_class__name)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2043_typeGen))).FSel((this).placebos__usize)).Apply(_2044_dimExprs);
              } else {
                r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2043_typeGen))).Apply(_2044_dimExprs);
              }
            }
            RAST._IExpr _out379;
            DCOMP._IOwnership _out380;
            (this).FromOwned(r, expectedOwnership, out _out379, out _out380);
            r = _out379;
            resultingOwnership = _out380;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_ArrayIndexToInt) {
          DAST._IExpression _2050_underlying = _source111.dtor_value;
          {
            RAST._IExpr _2051_recursiveGen;
            DCOMP._IOwnership _2052___v168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2053_recIdents;
            RAST._IExpr _out381;
            DCOMP._IOwnership _out382;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
            (this).GenExpr(_2050_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out381, out _out382, out _out383);
            _2051_recursiveGen = _out381;
            _2052___v168 = _out382;
            _2053_recIdents = _out383;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(_2051_recursiveGen);
            readIdents = _2053_recIdents;
            RAST._IExpr _out384;
            DCOMP._IOwnership _out385;
            (this).FromOwned(r, expectedOwnership, out _out384, out _out385);
            r = _out384;
            resultingOwnership = _out385;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_FinalizeNewArray) {
          DAST._IExpression _2054_underlying = _source111.dtor_value;
          DAST._IType _2055_typ = _source111.dtor_typ;
          {
            RAST._IType _2056_tpe;
            RAST._IType _out386;
            _out386 = (this).GenType(_2055_typ, DCOMP.GenTypeContext.@default());
            _2056_tpe = _out386;
            RAST._IExpr _2057_recursiveGen;
            DCOMP._IOwnership _2058___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2059_recIdents;
            RAST._IExpr _out387;
            DCOMP._IOwnership _out388;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
            (this).GenExpr(_2054_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out387, out _out388, out _out389);
            _2057_recursiveGen = _out387;
            _2058___v169 = _out388;
            _2059_recIdents = _out389;
            readIdents = _2059_recIdents;
            if ((_2056_tpe).IsObjectOrPointer()) {
              RAST._IType _2060_t;
              _2060_t = (_2056_tpe).ObjectOrPointerUnderlying();
              if ((_2060_t).is_Array) {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).array__construct)).Apply1(_2057_recursiveGen);
              } else if ((_2060_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _2061_c;
                _2061_c = (_2060_t).MultiArrayClass();
                r = ((((RAST.__default.dafny__runtime).MSel(_2061_c)).AsExpr()).FSel((this).array__construct)).Apply1(_2057_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_2056_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_2056_tpe)._ToString(DCOMP.__default.IND)));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            }
            RAST._IExpr _out390;
            DCOMP._IOwnership _out391;
            (this).FromOwned(r, expectedOwnership, out _out390, out _out391);
            r = _out390;
            resultingOwnership = _out391;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_DatatypeValue) {
          DAST._IResolvedType _2062_datatypeType = _source111.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _2063_typeArgs = _source111.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _2064_variant = _source111.dtor_variant;
          bool _2065_isCo = _source111.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _2066_values = _source111.dtor_contents;
          {
            RAST._IExpr _out392;
            _out392 = DCOMP.COMP.GenPathExpr((_2062_datatypeType).dtor_path, true);
            r = _out392;
            Dafny.ISequence<RAST._IType> _2067_genTypeArgs;
            _2067_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi45 = new BigInteger((_2063_typeArgs).Count);
            for (BigInteger _2068_i = BigInteger.Zero; _2068_i < _hi45; _2068_i++) {
              RAST._IType _2069_typeExpr;
              RAST._IType _out393;
              _out393 = (this).GenType((_2063_typeArgs).Select(_2068_i), DCOMP.GenTypeContext.@default());
              _2069_typeExpr = _out393;
              _2067_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_2067_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_2069_typeExpr));
            }
            if ((new BigInteger((_2063_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_2067_genTypeArgs);
            }
            r = (r).FSel(DCOMP.__default.escapeName(_2064_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _2070_assignments;
            _2070_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi46 = new BigInteger((_2066_values).Count);
            for (BigInteger _2071_i = BigInteger.Zero; _2071_i < _hi46; _2071_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs69 = (_2066_values).Select(_2071_i);
              Dafny.ISequence<Dafny.Rune> _2072_name = _let_tmp_rhs69.dtor__0;
              DAST._IExpression _2073_value = _let_tmp_rhs69.dtor__1;
              if (_2065_isCo) {
                RAST._IExpr _2074_recursiveGen;
                DCOMP._IOwnership _2075___v170;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2076_recIdents;
                RAST._IExpr _out394;
                DCOMP._IOwnership _out395;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out396;
                (this).GenExpr(_2073_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out394, out _out395, out _out396);
                _2074_recursiveGen = _out394;
                _2075___v170 = _out395;
                _2076_recIdents = _out396;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2076_recIdents);
                Dafny.ISequence<Dafny.Rune> _2077_allReadCloned;
                _2077_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_2076_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _2078_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2076_recIdents).Elements) {
                    _2078_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                    if ((_2076_recIdents).Contains(_2078_next)) {
                      goto after__ASSIGN_SUCH_THAT_3;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4740)");
                after__ASSIGN_SUCH_THAT_3: ;
                  _2077_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2077_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _2078_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _2078_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _2076_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2076_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2078_next));
                }
                Dafny.ISequence<Dafny.Rune> _2079_wasAssigned;
                _2079_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _2077_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_2074_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _2070_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2070_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_2072_name), RAST.Expr.create_RawExpr(_2079_wasAssigned))));
              } else {
                RAST._IExpr _2080_recursiveGen;
                DCOMP._IOwnership _2081___v171;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2082_recIdents;
                RAST._IExpr _out397;
                DCOMP._IOwnership _out398;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out399;
                (this).GenExpr(_2073_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out397, out _out398, out _out399);
                _2080_recursiveGen = _out397;
                _2081___v171 = _out398;
                _2082_recIdents = _out399;
                _2070_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_2070_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_2072_name), _2080_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2082_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _2070_assignments);
            if ((this).IsRcWrapped((_2062_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out400;
            DCOMP._IOwnership _out401;
            (this).FromOwned(r, expectedOwnership, out _out400, out _out401);
            r = _out400;
            resultingOwnership = _out401;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_Convert) {
          {
            RAST._IExpr _out402;
            DCOMP._IOwnership _out403;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out404;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out402, out _out403, out _out404);
            r = _out402;
            resultingOwnership = _out403;
            readIdents = _out404;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_SeqConstruct) {
          DAST._IExpression _2083_length = _source111.dtor_length;
          DAST._IExpression _2084_expr = _source111.dtor_elem;
          {
            RAST._IExpr _2085_recursiveGen;
            DCOMP._IOwnership _2086___v175;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2087_recIdents;
            RAST._IExpr _out405;
            DCOMP._IOwnership _out406;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out407;
            (this).GenExpr(_2084_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out405, out _out406, out _out407);
            _2085_recursiveGen = _out405;
            _2086___v175 = _out406;
            _2087_recIdents = _out407;
            RAST._IExpr _2088_lengthGen;
            DCOMP._IOwnership _2089___v176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2090_lengthIdents;
            RAST._IExpr _out408;
            DCOMP._IOwnership _out409;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out410;
            (this).GenExpr(_2083_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out408, out _out409, out _out410);
            _2088_lengthGen = _out408;
            _2089___v176 = _out409;
            _2090_lengthIdents = _out410;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_2085_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_2088_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2087_recIdents, _2090_lengthIdents);
            RAST._IExpr _out411;
            DCOMP._IOwnership _out412;
            (this).FromOwned(r, expectedOwnership, out _out411, out _out412);
            r = _out411;
            resultingOwnership = _out412;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _2091_exprs = _source111.dtor_elements;
          DAST._IType _2092_typ = _source111.dtor_typ;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _2093_genTpe;
            RAST._IType _out413;
            _out413 = (this).GenType(_2092_typ, DCOMP.GenTypeContext.@default());
            _2093_genTpe = _out413;
            BigInteger _2094_i;
            _2094_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2095_args;
            _2095_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2094_i) < (new BigInteger((_2091_exprs).Count))) {
              RAST._IExpr _2096_recursiveGen;
              DCOMP._IOwnership _2097___v177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2098_recIdents;
              RAST._IExpr _out414;
              DCOMP._IOwnership _out415;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out416;
              (this).GenExpr((_2091_exprs).Select(_2094_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out414, out _out415, out _out416);
              _2096_recursiveGen = _out414;
              _2097___v177 = _out415;
              _2098_recIdents = _out416;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2098_recIdents);
              _2095_args = Dafny.Sequence<RAST._IExpr>.Concat(_2095_args, Dafny.Sequence<RAST._IExpr>.FromElements(_2096_recursiveGen));
              _2094_i = (_2094_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).AsExpr()).Apply(_2095_args);
            if ((new BigInteger((_2095_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType()).Apply1(_2093_genTpe));
            }
            RAST._IExpr _out417;
            DCOMP._IOwnership _out418;
            (this).FromOwned(r, expectedOwnership, out _out417, out _out418);
            r = _out417;
            resultingOwnership = _out418;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _2099_exprs = _source111.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _2100_generatedValues;
            _2100_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2101_i;
            _2101_i = BigInteger.Zero;
            while ((_2101_i) < (new BigInteger((_2099_exprs).Count))) {
              RAST._IExpr _2102_recursiveGen;
              DCOMP._IOwnership _2103___v178;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2104_recIdents;
              RAST._IExpr _out419;
              DCOMP._IOwnership _out420;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out421;
              (this).GenExpr((_2099_exprs).Select(_2101_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out419, out _out420, out _out421);
              _2102_recursiveGen = _out419;
              _2103___v178 = _out420;
              _2104_recIdents = _out421;
              _2100_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2100_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2102_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2104_recIdents);
              _2101_i = (_2101_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).AsExpr()).Apply(_2100_generatedValues);
            RAST._IExpr _out422;
            DCOMP._IOwnership _out423;
            (this).FromOwned(r, expectedOwnership, out _out422, out _out423);
            r = _out422;
            resultingOwnership = _out423;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _2105_exprs = _source111.dtor_elements;
          {
            Dafny.ISequence<RAST._IExpr> _2106_generatedValues;
            _2106_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2107_i;
            _2107_i = BigInteger.Zero;
            while ((_2107_i) < (new BigInteger((_2105_exprs).Count))) {
              RAST._IExpr _2108_recursiveGen;
              DCOMP._IOwnership _2109___v179;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2110_recIdents;
              RAST._IExpr _out424;
              DCOMP._IOwnership _out425;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out426;
              (this).GenExpr((_2105_exprs).Select(_2107_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out424, out _out425, out _out426);
              _2108_recursiveGen = _out424;
              _2109___v179 = _out425;
              _2110_recIdents = _out426;
              _2106_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2106_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2108_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2110_recIdents);
              _2107_i = (_2107_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).AsExpr()).Apply(_2106_generatedValues);
            RAST._IExpr _out427;
            DCOMP._IOwnership _out428;
            (this).FromOwned(r, expectedOwnership, out _out427, out _out428);
            r = _out427;
            resultingOwnership = _out428;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_ToMultiset) {
          DAST._IExpression _2111_expr = _source111.dtor_ToMultiset_a0;
          {
            RAST._IExpr _2112_recursiveGen;
            DCOMP._IOwnership _2113___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2114_recIdents;
            RAST._IExpr _out429;
            DCOMP._IOwnership _out430;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out431;
            (this).GenExpr(_2111_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out429, out _out430, out _out431);
            _2112_recursiveGen = _out429;
            _2113___v180 = _out430;
            _2114_recIdents = _out431;
            r = ((_2112_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2114_recIdents;
            RAST._IExpr _out432;
            DCOMP._IOwnership _out433;
            (this).FromOwned(r, expectedOwnership, out _out432, out _out433);
            r = _out432;
            resultingOwnership = _out433;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2115_mapElems = _source111.dtor_mapElems;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _2116_generatedValues;
            _2116_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2117_i;
            _2117_i = BigInteger.Zero;
            while ((_2117_i) < (new BigInteger((_2115_mapElems).Count))) {
              RAST._IExpr _2118_recursiveGenKey;
              DCOMP._IOwnership _2119___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2120_recIdentsKey;
              RAST._IExpr _out434;
              DCOMP._IOwnership _out435;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
              (this).GenExpr(((_2115_mapElems).Select(_2117_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out434, out _out435, out _out436);
              _2118_recursiveGenKey = _out434;
              _2119___v181 = _out435;
              _2120_recIdentsKey = _out436;
              RAST._IExpr _2121_recursiveGenValue;
              DCOMP._IOwnership _2122___v182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2123_recIdentsValue;
              RAST._IExpr _out437;
              DCOMP._IOwnership _out438;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
              (this).GenExpr(((_2115_mapElems).Select(_2117_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out437, out _out438, out _out439);
              _2121_recursiveGenValue = _out437;
              _2122___v182 = _out438;
              _2123_recIdentsValue = _out439;
              _2116_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_2116_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_2118_recursiveGenKey, _2121_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2120_recIdentsKey), _2123_recIdentsValue);
              _2117_i = (_2117_i) + (BigInteger.One);
            }
            _2117_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2124_arguments;
            _2124_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2117_i) < (new BigInteger((_2116_generatedValues).Count))) {
              RAST._IExpr _2125_genKey;
              _2125_genKey = ((_2116_generatedValues).Select(_2117_i)).dtor__0;
              RAST._IExpr _2126_genValue;
              _2126_genValue = ((_2116_generatedValues).Select(_2117_i)).dtor__1;
              _2124_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2124_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _2125_genKey, _2126_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _2117_i = (_2117_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).AsExpr()).Apply(_2124_arguments);
            RAST._IExpr _out440;
            DCOMP._IOwnership _out441;
            (this).FromOwned(r, expectedOwnership, out _out440, out _out441);
            r = _out440;
            resultingOwnership = _out441;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_SeqUpdate) {
          DAST._IExpression _2127_expr = _source111.dtor_expr;
          DAST._IExpression _2128_index = _source111.dtor_indexExpr;
          DAST._IExpression _2129_value = _source111.dtor_value;
          {
            RAST._IExpr _2130_exprR;
            DCOMP._IOwnership _2131___v183;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2132_exprIdents;
            RAST._IExpr _out442;
            DCOMP._IOwnership _out443;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out444;
            (this).GenExpr(_2127_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out442, out _out443, out _out444);
            _2130_exprR = _out442;
            _2131___v183 = _out443;
            _2132_exprIdents = _out444;
            RAST._IExpr _2133_indexR;
            DCOMP._IOwnership _2134_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2135_indexIdents;
            RAST._IExpr _out445;
            DCOMP._IOwnership _out446;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
            (this).GenExpr(_2128_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out445, out _out446, out _out447);
            _2133_indexR = _out445;
            _2134_indexOwnership = _out446;
            _2135_indexIdents = _out447;
            RAST._IExpr _2136_valueR;
            DCOMP._IOwnership _2137_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2138_valueIdents;
            RAST._IExpr _out448;
            DCOMP._IOwnership _out449;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out450;
            (this).GenExpr(_2129_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out448, out _out449, out _out450);
            _2136_valueR = _out448;
            _2137_valueOwnership = _out449;
            _2138_valueIdents = _out450;
            r = ((_2130_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2133_indexR, _2136_valueR));
            RAST._IExpr _out451;
            DCOMP._IOwnership _out452;
            (this).FromOwned(r, expectedOwnership, out _out451, out _out452);
            r = _out451;
            resultingOwnership = _out452;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2132_exprIdents, _2135_indexIdents), _2138_valueIdents);
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_MapUpdate) {
          DAST._IExpression _2139_expr = _source111.dtor_expr;
          DAST._IExpression _2140_index = _source111.dtor_indexExpr;
          DAST._IExpression _2141_value = _source111.dtor_value;
          {
            RAST._IExpr _2142_exprR;
            DCOMP._IOwnership _2143___v184;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2144_exprIdents;
            RAST._IExpr _out453;
            DCOMP._IOwnership _out454;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out455;
            (this).GenExpr(_2139_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out453, out _out454, out _out455);
            _2142_exprR = _out453;
            _2143___v184 = _out454;
            _2144_exprIdents = _out455;
            RAST._IExpr _2145_indexR;
            DCOMP._IOwnership _2146_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2147_indexIdents;
            RAST._IExpr _out456;
            DCOMP._IOwnership _out457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out458;
            (this).GenExpr(_2140_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out456, out _out457, out _out458);
            _2145_indexR = _out456;
            _2146_indexOwnership = _out457;
            _2147_indexIdents = _out458;
            RAST._IExpr _2148_valueR;
            DCOMP._IOwnership _2149_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2150_valueIdents;
            RAST._IExpr _out459;
            DCOMP._IOwnership _out460;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out461;
            (this).GenExpr(_2141_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out459, out _out460, out _out461);
            _2148_valueR = _out459;
            _2149_valueOwnership = _out460;
            _2150_valueIdents = _out461;
            r = ((_2142_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2145_indexR, _2148_valueR));
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            (this).FromOwned(r, expectedOwnership, out _out462, out _out463);
            r = _out462;
            resultingOwnership = _out463;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2144_exprIdents, _2147_indexIdents), _2150_valueIdents);
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_This) {
          {
            DCOMP._ISelfInfo _source112 = selfIdent;
            {
              if (_source112.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _2151_id = _source112.dtor_rSelfName;
                DAST._IType _2152_dafnyType = _source112.dtor_dafnyType;
                {
                  RAST._IExpr _out464;
                  DCOMP._IOwnership _out465;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
                  (this).GenIdent(_2151_id, selfIdent, env, expectedOwnership, out _out464, out _out465, out _out466);
                  r = _out464;
                  resultingOwnership = _out465;
                  readIdents = _out466;
                }
                goto after_match42;
              }
            }
            {
              DCOMP._ISelfInfo _2153_None = _source112;
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
          after_match42: ;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_Ite) {
          DAST._IExpression _2154_cond = _source111.dtor_cond;
          DAST._IExpression _2155_t = _source111.dtor_thn;
          DAST._IExpression _2156_f = _source111.dtor_els;
          {
            RAST._IExpr _2157_cond;
            DCOMP._IOwnership _2158___v185;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2159_recIdentsCond;
            RAST._IExpr _out469;
            DCOMP._IOwnership _out470;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out471;
            (this).GenExpr(_2154_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out469, out _out470, out _out471);
            _2157_cond = _out469;
            _2158___v185 = _out470;
            _2159_recIdentsCond = _out471;
            RAST._IExpr _2160_fExpr;
            DCOMP._IOwnership _2161_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2162_recIdentsF;
            RAST._IExpr _out472;
            DCOMP._IOwnership _out473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
            (this).GenExpr(_2156_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out472, out _out473, out _out474);
            _2160_fExpr = _out472;
            _2161_fOwned = _out473;
            _2162_recIdentsF = _out474;
            RAST._IExpr _2163_tExpr;
            DCOMP._IOwnership _2164___v186;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2165_recIdentsT;
            RAST._IExpr _out475;
            DCOMP._IOwnership _out476;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out477;
            (this).GenExpr(_2155_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out475, out _out476, out _out477);
            _2163_tExpr = _out475;
            _2164___v186 = _out476;
            _2165_recIdentsT = _out477;
            r = RAST.Expr.create_IfExpr(_2157_cond, _2163_tExpr, _2160_fExpr);
            RAST._IExpr _out478;
            DCOMP._IOwnership _out479;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out478, out _out479);
            r = _out478;
            resultingOwnership = _out479;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2159_recIdentsCond, _2165_recIdentsT), _2162_recIdentsF);
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source111.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _2166_e = _source111.dtor_expr;
            DAST.Format._IUnaryOpFormat _2167_format = _source111.dtor_format1;
            {
              RAST._IExpr _2168_recursiveGen;
              DCOMP._IOwnership _2169___v187;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2170_recIdents;
              RAST._IExpr _out480;
              DCOMP._IOwnership _out481;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out482;
              (this).GenExpr(_2166_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out480, out _out481, out _out482);
              _2168_recursiveGen = _out480;
              _2169___v187 = _out481;
              _2170_recIdents = _out482;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _2168_recursiveGen, _2167_format);
              RAST._IExpr _out483;
              DCOMP._IOwnership _out484;
              (this).FromOwned(r, expectedOwnership, out _out483, out _out484);
              r = _out483;
              resultingOwnership = _out484;
              readIdents = _2170_recIdents;
              return ;
            }
            goto after_match41;
          }
        }
      }
      {
        if (_source111.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source111.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _2171_e = _source111.dtor_expr;
            DAST.Format._IUnaryOpFormat _2172_format = _source111.dtor_format1;
            {
              RAST._IExpr _2173_recursiveGen;
              DCOMP._IOwnership _2174___v188;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2175_recIdents;
              RAST._IExpr _out485;
              DCOMP._IOwnership _out486;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out487;
              (this).GenExpr(_2171_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out485, out _out486, out _out487);
              _2173_recursiveGen = _out485;
              _2174___v188 = _out486;
              _2175_recIdents = _out487;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _2173_recursiveGen, _2172_format);
              RAST._IExpr _out488;
              DCOMP._IOwnership _out489;
              (this).FromOwned(r, expectedOwnership, out _out488, out _out489);
              r = _out488;
              resultingOwnership = _out489;
              readIdents = _2175_recIdents;
              return ;
            }
            goto after_match41;
          }
        }
      }
      {
        if (_source111.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source111.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _2176_e = _source111.dtor_expr;
            DAST.Format._IUnaryOpFormat _2177_format = _source111.dtor_format1;
            {
              RAST._IExpr _2178_recursiveGen;
              DCOMP._IOwnership _2179_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2180_recIdents;
              RAST._IExpr _out490;
              DCOMP._IOwnership _out491;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out492;
              (this).GenExpr(_2176_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out490, out _out491, out _out492);
              _2178_recursiveGen = _out490;
              _2179_recOwned = _out491;
              _2180_recIdents = _out492;
              r = ((_2178_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out493;
              DCOMP._IOwnership _out494;
              (this).FromOwned(r, expectedOwnership, out _out493, out _out494);
              r = _out493;
              resultingOwnership = _out494;
              readIdents = _2180_recIdents;
              return ;
            }
            goto after_match41;
          }
        }
      }
      {
        if (_source111.is_BinOp) {
          RAST._IExpr _out495;
          DCOMP._IOwnership _out496;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out497;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out495, out _out496, out _out497);
          r = _out495;
          resultingOwnership = _out496;
          readIdents = _out497;
          goto after_match41;
        }
      }
      {
        if (_source111.is_ArrayLen) {
          DAST._IExpression _2181_expr = _source111.dtor_expr;
          DAST._IType _2182_exprType = _source111.dtor_exprType;
          BigInteger _2183_dim = _source111.dtor_dim;
          bool _2184_native = _source111.dtor_native;
          {
            RAST._IExpr _2185_recursiveGen;
            DCOMP._IOwnership _2186___v193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2187_recIdents;
            RAST._IExpr _out498;
            DCOMP._IOwnership _out499;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
            (this).GenExpr(_2181_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out498, out _out499, out _out500);
            _2185_recursiveGen = _out498;
            _2186___v193 = _out499;
            _2187_recIdents = _out500;
            RAST._IType _2188_arrayType;
            RAST._IType _out501;
            _out501 = (this).GenType(_2182_exprType, DCOMP.GenTypeContext.@default());
            _2188_arrayType = _out501;
            if (!((_2188_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2189_msg;
              _2189_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2188_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2189_msg);
              r = RAST.Expr.create_RawExpr(_2189_msg);
            } else {
              RAST._IType _2190_underlying;
              _2190_underlying = (_2188_arrayType).ObjectOrPointerUnderlying();
              if (((_2183_dim).Sign == 0) && ((_2190_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2185_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2183_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2185_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_2185_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_2183_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_2184_native)) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(r);
              }
            }
            RAST._IExpr _out502;
            DCOMP._IOwnership _out503;
            (this).FromOwned(r, expectedOwnership, out _out502, out _out503);
            r = _out502;
            resultingOwnership = _out503;
            readIdents = _2187_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_MapKeys) {
          DAST._IExpression _2191_expr = _source111.dtor_expr;
          {
            RAST._IExpr _2192_recursiveGen;
            DCOMP._IOwnership _2193___v194;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2194_recIdents;
            RAST._IExpr _out504;
            DCOMP._IOwnership _out505;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out506;
            (this).GenExpr(_2191_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out504, out _out505, out _out506);
            _2192_recursiveGen = _out504;
            _2193___v194 = _out505;
            _2194_recIdents = _out506;
            readIdents = _2194_recIdents;
            r = ((_2192_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out507;
            DCOMP._IOwnership _out508;
            (this).FromOwned(r, expectedOwnership, out _out507, out _out508);
            r = _out507;
            resultingOwnership = _out508;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_MapValues) {
          DAST._IExpression _2195_expr = _source111.dtor_expr;
          {
            RAST._IExpr _2196_recursiveGen;
            DCOMP._IOwnership _2197___v195;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2198_recIdents;
            RAST._IExpr _out509;
            DCOMP._IOwnership _out510;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out511;
            (this).GenExpr(_2195_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out509, out _out510, out _out511);
            _2196_recursiveGen = _out509;
            _2197___v195 = _out510;
            _2198_recIdents = _out511;
            readIdents = _2198_recIdents;
            r = ((_2196_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out512;
            DCOMP._IOwnership _out513;
            (this).FromOwned(r, expectedOwnership, out _out512, out _out513);
            r = _out512;
            resultingOwnership = _out513;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_MapItems) {
          DAST._IExpression _2199_expr = _source111.dtor_expr;
          {
            RAST._IExpr _2200_recursiveGen;
            DCOMP._IOwnership _2201___v196;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2202_recIdents;
            RAST._IExpr _out514;
            DCOMP._IOwnership _out515;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out516;
            (this).GenExpr(_2199_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out514, out _out515, out _out516);
            _2200_recursiveGen = _out514;
            _2201___v196 = _out515;
            _2202_recIdents = _out516;
            readIdents = _2202_recIdents;
            r = ((_2200_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("items"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out517;
            DCOMP._IOwnership _out518;
            (this).FromOwned(r, expectedOwnership, out _out517, out _out518);
            r = _out517;
            resultingOwnership = _out518;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_SelectFn) {
          DAST._IExpression _2203_on = _source111.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2204_field = _source111.dtor_field;
          bool _2205_isDatatype = _source111.dtor_onDatatype;
          bool _2206_isStatic = _source111.dtor_isStatic;
          bool _2207_isConstant = _source111.dtor_isConstant;
          Dafny.ISequence<DAST._IType> _2208_arguments = _source111.dtor_arguments;
          {
            RAST._IExpr _2209_onExpr;
            DCOMP._IOwnership _2210_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2211_recIdents;
            RAST._IExpr _out519;
            DCOMP._IOwnership _out520;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
            (this).GenExpr(_2203_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out519, out _out520, out _out521);
            _2209_onExpr = _out519;
            _2210_onOwned = _out520;
            _2211_recIdents = _out521;
            Dafny.ISequence<Dafny.Rune> _2212_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2213_onString;
            _2213_onString = (_2209_onExpr)._ToString(DCOMP.__default.IND);
            if (_2206_isStatic) {
              DCOMP._IEnvironment _2214_lEnv;
              _2214_lEnv = env;
              Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>> _2215_args;
              _2215_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements();
              _2212_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|");
              BigInteger _hi47 = new BigInteger((_2208_arguments).Count);
              for (BigInteger _2216_i = BigInteger.Zero; _2216_i < _hi47; _2216_i++) {
                if ((_2216_i).Sign == 1) {
                  _2212_s = Dafny.Sequence<Dafny.Rune>.Concat(_2212_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                RAST._IType _2217_ty;
                RAST._IType _out522;
                _out522 = (this).GenType((_2208_arguments).Select(_2216_i), DCOMP.GenTypeContext.@default());
                _2217_ty = _out522;
                RAST._IType _2218_bTy;
                _2218_bTy = RAST.Type.create_Borrowed(_2217_ty);
                Dafny.ISequence<Dafny.Rune> _2219_name;
                _2219_name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), Std.Strings.__default.OfInt(_2216_i));
                _2214_lEnv = (_2214_lEnv).AddAssigned(_2219_name, _2218_bTy);
                _2215_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.Concat(_2215_args, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>.create(_2219_name, _2217_ty)));
                _2212_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2212_s, _2219_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_2218_bTy)._ToString(DCOMP.__default.IND));
              }
              _2212_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2212_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| ")), _2213_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeVar(_2204_field)), ((_2207_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("));
              BigInteger _hi48 = new BigInteger((_2215_args).Count);
              for (BigInteger _2220_i = BigInteger.Zero; _2220_i < _hi48; _2220_i++) {
                if ((_2220_i).Sign == 1) {
                  _2212_s = Dafny.Sequence<Dafny.Rune>.Concat(_2212_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType> _let_tmp_rhs70 = (_2215_args).Select(_2220_i);
                Dafny.ISequence<Dafny.Rune> _2221_name = _let_tmp_rhs70.dtor__0;
                RAST._IType _2222_ty = _let_tmp_rhs70.dtor__1;
                RAST._IExpr _2223_rIdent;
                DCOMP._IOwnership _2224___v197;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2225___v198;
                RAST._IExpr _out523;
                DCOMP._IOwnership _out524;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
                (this).GenIdent(_2221_name, selfIdent, _2214_lEnv, (((_2222_ty).CanReadWithoutClone()) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed())), out _out523, out _out524, out _out525);
                _2223_rIdent = _out523;
                _2224___v197 = _out524;
                _2225___v198 = _out525;
                _2212_s = Dafny.Sequence<Dafny.Rune>.Concat(_2212_s, (_2223_rIdent)._ToString(DCOMP.__default.IND));
              }
              _2212_s = Dafny.Sequence<Dafny.Rune>.Concat(_2212_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            } else {
              _2212_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2212_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2212_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2213_onString), ((object.Equals(_2210_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2226_args;
              _2226_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2227_i;
              _2227_i = BigInteger.Zero;
              while ((_2227_i) < (new BigInteger((_2208_arguments).Count))) {
                if ((_2227_i).Sign == 1) {
                  _2226_args = Dafny.Sequence<Dafny.Rune>.Concat(_2226_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2226_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2226_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2227_i));
                _2227_i = (_2227_i) + (BigInteger.One);
              }
              _2212_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2212_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2226_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2212_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2212_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeVar(_2204_field)), ((_2207_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2226_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2212_s = Dafny.Sequence<Dafny.Rune>.Concat(_2212_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2212_s = Dafny.Sequence<Dafny.Rune>.Concat(_2212_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2228_typeShape;
            _2228_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2229_i;
            _2229_i = BigInteger.Zero;
            while ((_2229_i) < (new BigInteger((_2208_arguments).Count))) {
              if ((_2229_i).Sign == 1) {
                _2228_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2228_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2228_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2228_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2229_i = (_2229_i) + (BigInteger.One);
            }
            _2228_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2228_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2212_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2212_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2228_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2212_s);
            RAST._IExpr _out526;
            DCOMP._IOwnership _out527;
            (this).FromOwned(r, expectedOwnership, out _out526, out _out527);
            r = _out526;
            resultingOwnership = _out527;
            readIdents = _2211_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_Select) {
          DAST._IExpression _2230_on = _source111.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2231_field = _source111.dtor_field;
          bool _2232_isConstant = _source111.dtor_isConstant;
          bool _2233_isDatatype = _source111.dtor_onDatatype;
          DAST._IType _2234_fieldType = _source111.dtor_fieldType;
          {
            if (((_2230_on).is_Companion) || ((_2230_on).is_ExternCompanion)) {
              RAST._IExpr _2235_onExpr;
              DCOMP._IOwnership _2236_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2237_recIdents;
              RAST._IExpr _out528;
              DCOMP._IOwnership _out529;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
              (this).GenExpr(_2230_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out528, out _out529, out _out530);
              _2235_onExpr = _out528;
              _2236_onOwned = _out529;
              _2237_recIdents = _out530;
              r = ((_2235_onExpr).FSel(DCOMP.__default.escapeVar(_2231_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out531;
              DCOMP._IOwnership _out532;
              (this).FromOwned(r, expectedOwnership, out _out531, out _out532);
              r = _out531;
              resultingOwnership = _out532;
              readIdents = _2237_recIdents;
              return ;
            } else if (_2233_isDatatype) {
              RAST._IExpr _2238_onExpr;
              DCOMP._IOwnership _2239_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2240_recIdents;
              RAST._IExpr _out533;
              DCOMP._IOwnership _out534;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
              (this).GenExpr(_2230_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out533, out _out534, out _out535);
              _2238_onExpr = _out533;
              _2239_onOwned = _out534;
              _2240_recIdents = _out535;
              r = ((_2238_onExpr).Sel(DCOMP.__default.escapeVar(_2231_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2241_typ;
              RAST._IType _out536;
              _out536 = (this).GenType(_2234_fieldType, DCOMP.GenTypeContext.@default());
              _2241_typ = _out536;
              RAST._IExpr _out537;
              DCOMP._IOwnership _out538;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out537, out _out538);
              r = _out537;
              resultingOwnership = _out538;
              readIdents = _2240_recIdents;
            } else {
              RAST._IExpr _2242_onExpr;
              DCOMP._IOwnership _2243_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2244_recIdents;
              RAST._IExpr _out539;
              DCOMP._IOwnership _out540;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
              (this).GenExpr(_2230_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out539, out _out540, out _out541);
              _2242_onExpr = _out539;
              _2243_onOwned = _out540;
              _2244_recIdents = _out541;
              r = _2242_onExpr;
              if (!object.Equals(_2242_onExpr, RAST.__default.self)) {
                RAST._IExpr _source113 = _2242_onExpr;
                {
                  if (_source113.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source113.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source113.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name8 = underlying5.dtor_name;
                        if (object.Equals(name8, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                          goto after_match43;
                        }
                      }
                    }
                  }
                }
                {
                }
              after_match43: ;
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeVar(_2231_field));
              if (_2232_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out542;
              DCOMP._IOwnership _out543;
              (this).FromOwned(r, expectedOwnership, out _out542, out _out543);
              r = _out542;
              resultingOwnership = _out543;
              readIdents = _2244_recIdents;
            }
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_Index) {
          DAST._IExpression _2245_on = _source111.dtor_expr;
          DAST._ICollKind _2246_collKind = _source111.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2247_indices = _source111.dtor_indices;
          {
            RAST._IExpr _2248_onExpr;
            DCOMP._IOwnership _2249_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2250_recIdents;
            RAST._IExpr _out544;
            DCOMP._IOwnership _out545;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out546;
            (this).GenExpr(_2245_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out544, out _out545, out _out546);
            _2248_onExpr = _out544;
            _2249_onOwned = _out545;
            _2250_recIdents = _out546;
            readIdents = _2250_recIdents;
            r = _2248_onExpr;
            bool _2251_hadArray;
            _2251_hadArray = false;
            if (object.Equals(_2246_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2251_hadArray = true;
              if ((new BigInteger((_2247_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi49 = new BigInteger((_2247_indices).Count);
            for (BigInteger _2252_i = BigInteger.Zero; _2252_i < _hi49; _2252_i++) {
              if (object.Equals(_2246_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2253_idx;
                DCOMP._IOwnership _2254_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2255_recIdentsIdx;
                RAST._IExpr _out547;
                DCOMP._IOwnership _out548;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
                (this).GenExpr((_2247_indices).Select(_2252_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out547, out _out548, out _out549);
                _2253_idx = _out547;
                _2254_idxOwned = _out548;
                _2255_recIdentsIdx = _out549;
                _2253_idx = RAST.__default.IntoUsize(_2253_idx);
                r = RAST.Expr.create_SelectIndex(r, _2253_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2255_recIdentsIdx);
              } else {
                RAST._IExpr _2256_idx;
                DCOMP._IOwnership _2257_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2258_recIdentsIdx;
                RAST._IExpr _out550;
                DCOMP._IOwnership _out551;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out552;
                (this).GenExpr((_2247_indices).Select(_2252_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out550, out _out551, out _out552);
                _2256_idx = _out550;
                _2257_idxOwned = _out551;
                _2258_recIdentsIdx = _out552;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2256_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2258_recIdentsIdx);
              }
            }
            if (_2251_hadArray) {
              r = (r).Clone();
            }
            RAST._IExpr _out553;
            DCOMP._IOwnership _out554;
            (this).FromOwned(r, expectedOwnership, out _out553, out _out554);
            r = _out553;
            resultingOwnership = _out554;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_IndexRange) {
          DAST._IExpression _2259_on = _source111.dtor_expr;
          bool _2260_isArray = _source111.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2261_low = _source111.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2262_high = _source111.dtor_high;
          {
            RAST._IExpr _2263_onExpr;
            DCOMP._IOwnership _2264_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2265_recIdents;
            RAST._IExpr _out555;
            DCOMP._IOwnership _out556;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
            (this).GenExpr(_2259_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out555, out _out556, out _out557);
            _2263_onExpr = _out555;
            _2264_onOwned = _out556;
            _2265_recIdents = _out557;
            readIdents = _2265_recIdents;
            Dafny.ISequence<Dafny.Rune> _2266_methodName;
            if ((_2261_low).is_Some) {
              if ((_2262_high).is_Some) {
                _2266_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice");
              } else {
                _2266_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop");
              }
            } else if ((_2262_high).is_Some) {
              _2266_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take");
            } else {
              _2266_methodName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
            }
            Dafny.ISequence<RAST._IExpr> _2267_arguments;
            _2267_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source114 = _2261_low;
            {
              if (_source114.is_Some) {
                DAST._IExpression _2268_l = _source114.dtor_value;
                {
                  RAST._IExpr _2269_lExpr;
                  DCOMP._IOwnership _2270___v201;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2271_recIdentsL;
                  RAST._IExpr _out558;
                  DCOMP._IOwnership _out559;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
                  (this).GenExpr(_2268_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out558, out _out559, out _out560);
                  _2269_lExpr = _out558;
                  _2270___v201 = _out559;
                  _2271_recIdentsL = _out560;
                  _2267_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2267_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2269_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2271_recIdentsL);
                }
                goto after_match44;
              }
            }
            {
            }
          after_match44: ;
            Std.Wrappers._IOption<DAST._IExpression> _source115 = _2262_high;
            {
              if (_source115.is_Some) {
                DAST._IExpression _2272_h = _source115.dtor_value;
                {
                  RAST._IExpr _2273_hExpr;
                  DCOMP._IOwnership _2274___v202;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2275_recIdentsH;
                  RAST._IExpr _out561;
                  DCOMP._IOwnership _out562;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
                  (this).GenExpr(_2272_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out561, out _out562, out _out563);
                  _2273_hExpr = _out561;
                  _2274___v202 = _out562;
                  _2275_recIdentsH = _out563;
                  _2267_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2267_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2273_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2275_recIdentsH);
                }
                goto after_match45;
              }
            }
            {
            }
          after_match45: ;
            r = _2263_onExpr;
            if (_2260_isArray) {
              if (!(_2266_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2266_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2266_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).FSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2266_methodName))).Apply(_2267_arguments);
            } else {
              if (!(_2266_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2266_methodName)).Apply(_2267_arguments);
              }
            }
            RAST._IExpr _out564;
            DCOMP._IOwnership _out565;
            (this).FromOwned(r, expectedOwnership, out _out564, out _out565);
            r = _out564;
            resultingOwnership = _out565;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_TupleSelect) {
          DAST._IExpression _2276_on = _source111.dtor_expr;
          BigInteger _2277_idx = _source111.dtor_index;
          DAST._IType _2278_fieldType = _source111.dtor_fieldType;
          {
            RAST._IExpr _2279_onExpr;
            DCOMP._IOwnership _2280_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2281_recIdents;
            RAST._IExpr _out566;
            DCOMP._IOwnership _out567;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
            (this).GenExpr(_2276_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out566, out _out567, out _out568);
            _2279_onExpr = _out566;
            _2280_onOwnership = _out567;
            _2281_recIdents = _out568;
            Dafny.ISequence<Dafny.Rune> _2282_selName;
            _2282_selName = Std.Strings.__default.OfNat(_2277_idx);
            DAST._IType _source116 = _2278_fieldType;
            {
              if (_source116.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2283_tps = _source116.dtor_Tuple_a0;
                if (((_2278_fieldType).is_Tuple) && ((new BigInteger((_2283_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2282_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2282_selName);
                }
                goto after_match46;
              }
            }
            {
            }
          after_match46: ;
            r = ((_2279_onExpr).Sel(_2282_selName)).Clone();
            RAST._IExpr _out569;
            DCOMP._IOwnership _out570;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out569, out _out570);
            r = _out569;
            resultingOwnership = _out570;
            readIdents = _2281_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_Call) {
          DAST._IExpression _2284_on = _source111.dtor_on;
          DAST._ICallName _2285_name = _source111.dtor_callName;
          Dafny.ISequence<DAST._IType> _2286_typeArgs = _source111.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2287_args = _source111.dtor_args;
          {
            Dafny.ISequence<RAST._IExpr> _2288_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2289_recIdents;
            Dafny.ISequence<RAST._IType> _2290_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2291_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out571;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out572;
            Dafny.ISequence<RAST._IType> _out573;
            Std.Wrappers._IOption<DAST._IResolvedType> _out574;
            (this).GenArgs(selfIdent, _2285_name, _2286_typeArgs, _2287_args, env, out _out571, out _out572, out _out573, out _out574);
            _2288_argExprs = _out571;
            _2289_recIdents = _out572;
            _2290_typeExprs = _out573;
            _2291_fullNameQualifier = _out574;
            readIdents = _2289_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source117 = _2291_fullNameQualifier;
            {
              if (_source117.is_Some) {
                DAST._IResolvedType value11 = _source117.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2292_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2293_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2294_base = value11.dtor_kind;
                RAST._IExpr _2295_fullPath;
                RAST._IExpr _out575;
                _out575 = DCOMP.COMP.GenPathExpr(_2292_path, true);
                _2295_fullPath = _out575;
                Dafny.ISequence<RAST._IType> _2296_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out576;
                _out576 = (this).GenTypeArgs(_2293_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2296_onTypeExprs = _out576;
                RAST._IExpr _2297_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2298_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2299_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2294_base).is_Trait) || ((_2294_base).is_Class)) {
                  RAST._IExpr _out577;
                  DCOMP._IOwnership _out578;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out579;
                  (this).GenExpr(_2284_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out577, out _out578, out _out579);
                  _2297_onExpr = _out577;
                  _2298_recOwnership = _out578;
                  _2299_recIdents = _out579;
                  _2297_onExpr = ((this).read__macro).Apply1(_2297_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2299_recIdents);
                } else {
                  RAST._IExpr _out580;
                  DCOMP._IOwnership _out581;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out582;
                  (this).GenExpr(_2284_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out580, out _out581, out _out582);
                  _2297_onExpr = _out580;
                  _2298_recOwnership = _out581;
                  _2299_recIdents = _out582;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2299_recIdents);
                }
                r = ((((_2295_fullPath).ApplyType(_2296_onTypeExprs)).FSel(DCOMP.__default.escapeName((_2285_name).dtor_name))).ApplyType(_2290_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2297_onExpr), _2288_argExprs));
                RAST._IExpr _out583;
                DCOMP._IOwnership _out584;
                (this).FromOwned(r, expectedOwnership, out _out583, out _out584);
                r = _out583;
                resultingOwnership = _out584;
                goto after_match47;
              }
            }
            {
              RAST._IExpr _2300_onExpr;
              DCOMP._IOwnership _2301___v208;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2302_recIdents;
              RAST._IExpr _out585;
              DCOMP._IOwnership _out586;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out587;
              (this).GenExpr(_2284_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out585, out _out586, out _out587);
              _2300_onExpr = _out585;
              _2301___v208 = _out586;
              _2302_recIdents = _out587;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2302_recIdents);
              Dafny.ISequence<Dafny.Rune> _2303_renderedName;
              _2303_renderedName = (this).GetMethodName(_2284_on, _2285_name);
              DAST._IExpression _source118 = _2284_on;
              {
                bool disjunctiveMatch15 = false;
                if (_source118.is_Companion) {
                  disjunctiveMatch15 = true;
                }
                if (_source118.is_ExternCompanion) {
                  disjunctiveMatch15 = true;
                }
                if (disjunctiveMatch15) {
                  {
                    _2300_onExpr = (_2300_onExpr).FSel(_2303_renderedName);
                  }
                  goto after_match48;
                }
              }
              {
                {
                  if (!object.Equals(_2300_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source119 = _2285_name;
                    {
                      if (_source119.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source119.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2304_tpe = onType2.dtor_value;
                          RAST._IType _2305_typ;
                          RAST._IType _out588;
                          _out588 = (this).GenType(_2304_tpe, DCOMP.GenTypeContext.@default());
                          _2305_typ = _out588;
                          if ((_2305_typ).IsObjectOrPointer()) {
                            _2300_onExpr = ((this).read__macro).Apply1(_2300_onExpr);
                          }
                          goto after_match49;
                        }
                      }
                    }
                    {
                    }
                  after_match49: ;
                  }
                  _2300_onExpr = (_2300_onExpr).Sel(_2303_renderedName);
                }
              }
            after_match48: ;
              r = ((_2300_onExpr).ApplyType(_2290_typeExprs)).Apply(_2288_argExprs);
              RAST._IExpr _out589;
              DCOMP._IOwnership _out590;
              (this).FromOwned(r, expectedOwnership, out _out589, out _out590);
              r = _out589;
              resultingOwnership = _out590;
              return ;
            }
          after_match47: ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2306_paramsDafny = _source111.dtor_params;
          DAST._IType _2307_retType = _source111.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2308_body = _source111.dtor_body;
          {
            Dafny.ISequence<RAST._IFormal> _2309_params;
            Dafny.ISequence<RAST._IFormal> _out591;
            _out591 = (this).GenParams(_2306_paramsDafny, true);
            _2309_params = _out591;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2310_paramNames;
            _2310_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2311_paramTypesMap;
            _2311_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi50 = new BigInteger((_2309_params).Count);
            for (BigInteger _2312_i = BigInteger.Zero; _2312_i < _hi50; _2312_i++) {
              Dafny.ISequence<Dafny.Rune> _2313_name;
              _2313_name = ((_2309_params).Select(_2312_i)).dtor_name;
              _2310_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2310_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2313_name));
              _2311_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2311_paramTypesMap, _2313_name, ((_2309_params).Select(_2312_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2314_subEnv;
            _2314_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2310_paramNames, _2311_paramTypesMap));
            RAST._IExpr _2315_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2316_recIdents;
            DCOMP._IEnvironment _2317___v218;
            RAST._IExpr _out592;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out593;
            DCOMP._IEnvironment _out594;
            (this).GenStmts(_2308_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2314_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out592, out _out593, out _out594);
            _2315_recursiveGen = _out592;
            _2316_recIdents = _out593;
            _2317___v218 = _out594;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2316_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2316_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2318_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll10 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_11 in (_2318_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2319_name = (Dafny.ISequence<Dafny.Rune>)_compr_11;
                if ((_2318_paramNames).Contains(_2319_name)) {
                  _coll10.Add(_2319_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll10);
            }))())(_2310_paramNames));
            RAST._IExpr _2320_allReadCloned;
            _2320_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2316_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2321_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_4 in (_2316_recIdents).Elements) {
                _2321_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_4;
                if ((_2316_recIdents).Contains(_2321_next)) {
                  goto after__ASSIGN_SUCH_THAT_4;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 5242)");
            after__ASSIGN_SUCH_THAT_4: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2321_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2322_selfCloned;
                DCOMP._IOwnership _2323___v219;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2324___v220;
                RAST._IExpr _out595;
                DCOMP._IOwnership _out596;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out597;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out595, out _out596, out _out597);
                _2322_selfCloned = _out595;
                _2323___v219 = _out596;
                _2324___v220 = _out597;
                _2320_allReadCloned = (_2320_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2322_selfCloned)));
              } else if (!((_2310_paramNames).Contains(_2321_next))) {
                RAST._IExpr _2325_copy;
                _2325_copy = (RAST.Expr.create_Identifier(_2321_next)).Clone();
                _2320_allReadCloned = (_2320_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2321_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2325_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2321_next));
              }
              _2316_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2316_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2321_next));
            }
            RAST._IType _2326_retTypeGen;
            RAST._IType _out598;
            _out598 = (this).GenType(_2307_retType, DCOMP.GenTypeContext.@default());
            _2326_retTypeGen = _out598;
            r = RAST.Expr.create_Block((_2320_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2309_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2326_retTypeGen), RAST.Expr.create_Block(_2315_recursiveGen)))));
            RAST._IExpr _out599;
            DCOMP._IOwnership _out600;
            (this).FromOwned(r, expectedOwnership, out _out599, out _out600);
            r = _out599;
            resultingOwnership = _out600;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2327_values = _source111.dtor_values;
          DAST._IType _2328_retType = _source111.dtor_retType;
          DAST._IExpression _2329_expr = _source111.dtor_expr;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2330_paramNames;
            _2330_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2331_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out601;
            _out601 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2332_value) => {
              return (_2332_value).dtor__0;
            })), _2327_values), false);
            _2331_paramFormals = _out601;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2333_paramTypes;
            _2333_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2334_paramNamesSet;
            _2334_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi51 = new BigInteger((_2327_values).Count);
            for (BigInteger _2335_i = BigInteger.Zero; _2335_i < _hi51; _2335_i++) {
              Dafny.ISequence<Dafny.Rune> _2336_name;
              _2336_name = (((_2327_values).Select(_2335_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2337_rName;
              _2337_rName = DCOMP.__default.escapeVar(_2336_name);
              _2330_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2330_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2337_rName));
              _2333_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2333_paramTypes, _2337_rName, ((_2331_paramFormals).Select(_2335_i)).dtor_tpe);
              _2334_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2334_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2337_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi52 = new BigInteger((_2327_values).Count);
            for (BigInteger _2338_i = BigInteger.Zero; _2338_i < _hi52; _2338_i++) {
              RAST._IType _2339_typeGen;
              RAST._IType _out602;
              _out602 = (this).GenType((((_2327_values).Select(_2338_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.@default());
              _2339_typeGen = _out602;
              RAST._IExpr _2340_valueGen;
              DCOMP._IOwnership _2341___v221;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2342_recIdents;
              RAST._IExpr _out603;
              DCOMP._IOwnership _out604;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out605;
              (this).GenExpr(((_2327_values).Select(_2338_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out603, out _out604, out _out605);
              _2340_valueGen = _out603;
              _2341___v221 = _out604;
              _2342_recIdents = _out605;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar((((_2327_values).Select(_2338_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2339_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2340_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2342_recIdents);
            }
            DCOMP._IEnvironment _2343_newEnv;
            _2343_newEnv = DCOMP.Environment.create(_2330_paramNames, _2333_paramTypes);
            RAST._IExpr _2344_recGen;
            DCOMP._IOwnership _2345_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2346_recIdents;
            RAST._IExpr _out606;
            DCOMP._IOwnership _out607;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out608;
            (this).GenExpr(_2329_expr, selfIdent, _2343_newEnv, expectedOwnership, out _out606, out _out607, out _out608);
            _2344_recGen = _out606;
            _2345_recOwned = _out607;
            _2346_recIdents = _out608;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2346_recIdents, _2334_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2344_recGen));
            RAST._IExpr _out609;
            DCOMP._IOwnership _out610;
            (this).FromOwnership(r, _2345_recOwned, expectedOwnership, out _out609, out _out610);
            r = _out609;
            resultingOwnership = _out610;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2347_name = _source111.dtor_ident;
          DAST._IType _2348_tpe = _source111.dtor_typ;
          DAST._IExpression _2349_value = _source111.dtor_value;
          DAST._IExpression _2350_iifeBody = _source111.dtor_iifeBody;
          {
            RAST._IExpr _2351_valueGen;
            DCOMP._IOwnership _2352___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2353_recIdents;
            RAST._IExpr _out611;
            DCOMP._IOwnership _out612;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out613;
            (this).GenExpr(_2349_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out611, out _out612, out _out613);
            _2351_valueGen = _out611;
            _2352___v222 = _out612;
            _2353_recIdents = _out613;
            readIdents = _2353_recIdents;
            RAST._IType _2354_valueTypeGen;
            RAST._IType _out614;
            _out614 = (this).GenType(_2348_tpe, DCOMP.GenTypeContext.@default());
            _2354_valueTypeGen = _out614;
            Dafny.ISequence<Dafny.Rune> _2355_iifeVar;
            _2355_iifeVar = DCOMP.__default.escapeVar(_2347_name);
            RAST._IExpr _2356_bodyGen;
            DCOMP._IOwnership _2357___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2358_bodyIdents;
            RAST._IExpr _out615;
            DCOMP._IOwnership _out616;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out617;
            (this).GenExpr(_2350_iifeBody, selfIdent, (env).AddAssigned(_2355_iifeVar, _2354_valueTypeGen), DCOMP.Ownership.create_OwnershipOwned(), out _out615, out _out616, out _out617);
            _2356_bodyGen = _out615;
            _2357___v223 = _out616;
            _2358_bodyIdents = _out617;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2358_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2355_iifeVar)));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _2355_iifeVar, Std.Wrappers.Option<RAST._IType>.create_Some(_2354_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2351_valueGen))).Then(_2356_bodyGen));
            RAST._IExpr _out618;
            DCOMP._IOwnership _out619;
            (this).FromOwned(r, expectedOwnership, out _out618, out _out619);
            r = _out618;
            resultingOwnership = _out619;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_Apply) {
          DAST._IExpression _2359_func = _source111.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2360_args = _source111.dtor_args;
          {
            RAST._IExpr _2361_funcExpr;
            DCOMP._IOwnership _2362___v224;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2363_recIdents;
            RAST._IExpr _out620;
            DCOMP._IOwnership _out621;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
            (this).GenExpr(_2359_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out620, out _out621, out _out622);
            _2361_funcExpr = _out620;
            _2362___v224 = _out621;
            _2363_recIdents = _out622;
            readIdents = _2363_recIdents;
            Dafny.ISequence<RAST._IExpr> _2364_rArgs;
            _2364_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi53 = new BigInteger((_2360_args).Count);
            for (BigInteger _2365_i = BigInteger.Zero; _2365_i < _hi53; _2365_i++) {
              RAST._IExpr _2366_argExpr;
              DCOMP._IOwnership _2367_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2368_argIdents;
              RAST._IExpr _out623;
              DCOMP._IOwnership _out624;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out625;
              (this).GenExpr((_2360_args).Select(_2365_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out623, out _out624, out _out625);
              _2366_argExpr = _out623;
              _2367_argOwned = _out624;
              _2368_argIdents = _out625;
              _2364_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2364_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2366_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2368_argIdents);
            }
            r = (_2361_funcExpr).Apply(_2364_rArgs);
            RAST._IExpr _out626;
            DCOMP._IOwnership _out627;
            (this).FromOwned(r, expectedOwnership, out _out626, out _out627);
            r = _out626;
            resultingOwnership = _out627;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_TypeTest) {
          DAST._IExpression _2369_on = _source111.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2370_dType = _source111.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2371_variant = _source111.dtor_variant;
          {
            RAST._IExpr _2372_exprGen;
            DCOMP._IOwnership _2373___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2374_recIdents;
            RAST._IExpr _out628;
            DCOMP._IOwnership _out629;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out630;
            (this).GenExpr(_2369_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out628, out _out629, out _out630);
            _2372_exprGen = _out628;
            _2373___v225 = _out629;
            _2374_recIdents = _out630;
            RAST._IType _2375_dTypePath;
            RAST._IType _out631;
            _out631 = DCOMP.COMP.GenPathType(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2370_dType, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2371_variant)));
            _2375_dTypePath = _out631;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2372_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_2375_dTypePath)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out632;
            DCOMP._IOwnership _out633;
            (this).FromOwned(r, expectedOwnership, out _out632, out _out633);
            r = _out632;
            resultingOwnership = _out633;
            readIdents = _2374_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_Is) {
          DAST._IExpression _2376_expr = _source111.dtor_expr;
          DAST._IType _2377_fromType = _source111.dtor_fromType;
          DAST._IType _2378_toType = _source111.dtor_toType;
          {
            RAST._IExpr _2379_expr;
            DCOMP._IOwnership _2380_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2381_recIdents;
            RAST._IExpr _out634;
            DCOMP._IOwnership _out635;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out636;
            (this).GenExpr(_2376_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out634, out _out635, out _out636);
            _2379_expr = _out634;
            _2380_recOwned = _out635;
            _2381_recIdents = _out636;
            RAST._IType _2382_fromType;
            RAST._IType _out637;
            _out637 = (this).GenType(_2377_fromType, DCOMP.GenTypeContext.@default());
            _2382_fromType = _out637;
            RAST._IType _2383_toType;
            RAST._IType _out638;
            _out638 = (this).GenType(_2378_toType, DCOMP.GenTypeContext.@default());
            _2383_toType = _out638;
            if (((_2382_fromType).IsObjectOrPointer()) && ((_2383_toType).IsObjectOrPointer())) {
              r = (((_2379_expr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is_instance_of"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((_2383_toType).ObjectOrPointerUnderlying()))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Source and/or target types of type test is/are not Object or Ptr"));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
            RAST._IExpr _out639;
            DCOMP._IOwnership _out640;
            (this).FromOwnership(r, _2380_recOwned, expectedOwnership, out _out639, out _out640);
            r = _out639;
            resultingOwnership = _out640;
            readIdents = _2381_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_BoolBoundedPool) {
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
          goto after_match41;
        }
      }
      {
        if (_source111.is_SetBoundedPool) {
          DAST._IExpression _2384_of = _source111.dtor_of;
          {
            RAST._IExpr _2385_exprGen;
            DCOMP._IOwnership _2386___v226;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2387_recIdents;
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out645;
            (this).GenExpr(_2384_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out643, out _out644, out _out645);
            _2385_exprGen = _out643;
            _2386___v226 = _out644;
            _2387_recIdents = _out645;
            r = ((_2385_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out646;
            DCOMP._IOwnership _out647;
            (this).FromOwned(r, expectedOwnership, out _out646, out _out647);
            r = _out646;
            resultingOwnership = _out647;
            readIdents = _2387_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_SeqBoundedPool) {
          DAST._IExpression _2388_of = _source111.dtor_of;
          bool _2389_includeDuplicates = _source111.dtor_includeDuplicates;
          {
            RAST._IExpr _2390_exprGen;
            DCOMP._IOwnership _2391___v227;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2392_recIdents;
            RAST._IExpr _out648;
            DCOMP._IOwnership _out649;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out650;
            (this).GenExpr(_2388_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out648, out _out649, out _out650);
            _2390_exprGen = _out648;
            _2391___v227 = _out649;
            _2392_recIdents = _out650;
            r = ((_2390_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2389_includeDuplicates)) {
              r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).AsExpr()).Apply1(r);
            }
            RAST._IExpr _out651;
            DCOMP._IOwnership _out652;
            (this).FromOwned(r, expectedOwnership, out _out651, out _out652);
            r = _out651;
            resultingOwnership = _out652;
            readIdents = _2392_recIdents;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_MapBoundedPool) {
          DAST._IExpression _2393_of = _source111.dtor_of;
          {
            RAST._IExpr _2394_exprGen;
            DCOMP._IOwnership _2395___v228;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2396_recIdents;
            RAST._IExpr _out653;
            DCOMP._IOwnership _out654;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
            (this).GenExpr(_2393_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out653, out _out654, out _out655);
            _2394_exprGen = _out653;
            _2395___v228 = _out654;
            _2396_recIdents = _out655;
            r = ((((_2394_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2396_recIdents;
            RAST._IExpr _out656;
            DCOMP._IOwnership _out657;
            (this).FromOwned(r, expectedOwnership, out _out656, out _out657);
            r = _out656;
            resultingOwnership = _out657;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_IntRange) {
          DAST._IExpression _2397_lo = _source111.dtor_lo;
          DAST._IExpression _2398_hi = _source111.dtor_hi;
          bool _2399_up = _source111.dtor_up;
          {
            RAST._IExpr _2400_lo;
            DCOMP._IOwnership _2401___v229;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2402_recIdentsLo;
            RAST._IExpr _out658;
            DCOMP._IOwnership _out659;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out660;
            (this).GenExpr(_2397_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out658, out _out659, out _out660);
            _2400_lo = _out658;
            _2401___v229 = _out659;
            _2402_recIdentsLo = _out660;
            RAST._IExpr _2403_hi;
            DCOMP._IOwnership _2404___v230;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2405_recIdentsHi;
            RAST._IExpr _out661;
            DCOMP._IOwnership _out662;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out663;
            (this).GenExpr(_2398_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out661, out _out662, out _out663);
            _2403_hi = _out661;
            _2404___v230 = _out662;
            _2405_recIdentsHi = _out663;
            if (_2399_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2400_lo, _2403_hi));
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2403_hi, _2400_lo));
            }
            RAST._IExpr _out664;
            DCOMP._IOwnership _out665;
            (this).FromOwned(r, expectedOwnership, out _out664, out _out665);
            r = _out664;
            resultingOwnership = _out665;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2402_recIdentsLo, _2405_recIdentsHi);
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_UnboundedIntRange) {
          DAST._IExpression _2406_start = _source111.dtor_start;
          bool _2407_up = _source111.dtor_up;
          {
            RAST._IExpr _2408_start;
            DCOMP._IOwnership _2409___v231;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2410_recIdentStart;
            RAST._IExpr _out666;
            DCOMP._IOwnership _out667;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out668;
            (this).GenExpr(_2406_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out666, out _out667, out _out668);
            _2408_start = _out666;
            _2409___v231 = _out667;
            _2410_recIdentStart = _out668;
            if (_2407_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).AsExpr()).Apply1(_2408_start);
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).AsExpr()).Apply1(_2408_start);
            }
            RAST._IExpr _out669;
            DCOMP._IOwnership _out670;
            (this).FromOwned(r, expectedOwnership, out _out669, out _out670);
            r = _out669;
            resultingOwnership = _out670;
            readIdents = _2410_recIdentStart;
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_MapBuilder) {
          DAST._IType _2411_keyType = _source111.dtor_keyType;
          DAST._IType _2412_valueType = _source111.dtor_valueType;
          {
            RAST._IType _2413_kType;
            RAST._IType _out671;
            _out671 = (this).GenType(_2411_keyType, DCOMP.GenTypeContext.@default());
            _2413_kType = _out671;
            RAST._IType _2414_vType;
            RAST._IType _out672;
            _out672 = (this).GenType(_2412_valueType, DCOMP.GenTypeContext.@default());
            _2414_vType = _out672;
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2413_kType, _2414_vType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out673;
            DCOMP._IOwnership _out674;
            (this).FromOwned(r, expectedOwnership, out _out673, out _out674);
            r = _out673;
            resultingOwnership = _out674;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
          goto after_match41;
        }
      }
      {
        if (_source111.is_SetBuilder) {
          DAST._IType _2415_elemType = _source111.dtor_elemType;
          {
            RAST._IType _2416_eType;
            RAST._IType _out675;
            _out675 = (this).GenType(_2415_elemType, DCOMP.GenTypeContext.@default());
            _2416_eType = _out675;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2416_eType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out676;
            DCOMP._IOwnership _out677;
            (this).FromOwned(r, expectedOwnership, out _out676, out _out677);
            r = _out676;
            resultingOwnership = _out677;
            return ;
          }
          goto after_match41;
        }
      }
      {
        DAST._IType _2417_elemType = _source111.dtor_elemType;
        DAST._IExpression _2418_collection = _source111.dtor_collection;
        bool _2419_is__forall = _source111.dtor_is__forall;
        DAST._IExpression _2420_lambda = _source111.dtor_lambda;
        {
          RAST._IType _2421_tpe;
          RAST._IType _out678;
          _out678 = (this).GenType(_2417_elemType, DCOMP.GenTypeContext.@default());
          _2421_tpe = _out678;
          RAST._IExpr _2422_collectionGen;
          DCOMP._IOwnership _2423___v232;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2424_recIdents;
          RAST._IExpr _out679;
          DCOMP._IOwnership _out680;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out681;
          (this).GenExpr(_2418_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out679, out _out680, out _out681);
          _2422_collectionGen = _out679;
          _2423___v232 = _out680;
          _2424_recIdents = _out681;
          Dafny.ISequence<DAST._IAttribute> _2425_extraAttributes;
          _2425_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2418_collection).is_IntRange) || ((_2418_collection).is_UnboundedIntRange)) || ((_2418_collection).is_SeqBoundedPool)) {
            _2425_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2420_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2426_formals;
            _2426_formals = (_2420_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2427_newFormals;
            _2427_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi54 = new BigInteger((_2426_formals).Count);
            for (BigInteger _2428_i = BigInteger.Zero; _2428_i < _hi54; _2428_i++) {
              var _pat_let_tv9 = _2425_extraAttributes;
              var _pat_let_tv10 = _2426_formals;
              _2427_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2427_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2426_formals).Select(_2428_i), _pat_let25_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let25_0, _2429_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv9, ((_pat_let_tv10).Select(_2428_i)).dtor_attributes), _pat_let26_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let26_0, _2430_dt__update_hattributes_h0 => DAST.Formal.create((_2429_dt__update__tmp_h0).dtor_name, (_2429_dt__update__tmp_h0).dtor_typ, _2430_dt__update_hattributes_h0)))))));
            }
            DAST._IExpression _2431_newLambda;
            DAST._IExpression _2432_dt__update__tmp_h1 = _2420_lambda;
            Dafny.ISequence<DAST._IFormal> _2433_dt__update_hparams_h0 = _2427_newFormals;
            _2431_newLambda = DAST.Expression.create_Lambda(_2433_dt__update_hparams_h0, (_2432_dt__update__tmp_h1).dtor_retType, (_2432_dt__update__tmp_h1).dtor_body);
            RAST._IExpr _2434_lambdaGen;
            DCOMP._IOwnership _2435___v233;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2436_recLambdaIdents;
            RAST._IExpr _out682;
            DCOMP._IOwnership _out683;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out684;
            (this).GenExpr(_2431_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out682, out _out683, out _out684);
            _2434_lambdaGen = _out682;
            _2435___v233 = _out683;
            _2436_recLambdaIdents = _out684;
            Dafny.ISequence<Dafny.Rune> _2437_fn;
            if (_2419_is__forall) {
              _2437_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all");
            } else {
              _2437_fn = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any");
            }
            r = ((_2422_collectionGen).Sel(_2437_fn)).Apply1(((_2434_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2424_recIdents, _2436_recLambdaIdents);
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
    after_match41: ;
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> externalFiles)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      Dafny.ISequence<RAST._IModDecl> _2438_externUseDecls;
      _2438_externUseDecls = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi55 = new BigInteger((externalFiles).Count);
      for (BigInteger _2439_i = BigInteger.Zero; _2439_i < _hi55; _2439_i++) {
        Dafny.ISequence<Dafny.Rune> _2440_externalFile;
        _2440_externalFile = (externalFiles).Select(_2439_i);
        Dafny.ISequence<Dafny.Rune> _2441_externalMod;
        _2441_externalMod = _2440_externalFile;
        if (((new BigInteger((_2440_externalFile).Count)) > (new BigInteger(3))) && (((_2440_externalFile).Drop((new BigInteger((_2440_externalFile).Count)) - (new BigInteger(3)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".rs")))) {
          _2441_externalMod = (_2440_externalFile).Subsequence(BigInteger.Zero, (new BigInteger((_2440_externalFile).Count)) - (new BigInteger(3)));
        } else {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unrecognized external file "), _2440_externalFile), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". External file must be *.rs files")));
        }
        RAST._IMod _2442_externMod;
        _2442_externMod = RAST.Mod.create_ExternMod(_2441_externalMod);
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (_2442_externMod)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        _2438_externUseDecls = Dafny.Sequence<RAST._IModDecl>.Concat(_2438_externUseDecls, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), ((RAST.__default.crate).MSel(_2441_externalMod)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))));
      }
      if (!(_2438_externUseDecls).Equals(Dafny.Sequence<RAST._IModDecl>.FromElements())) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (RAST.Mod.create_Mod(DCOMP.COMP.DAFNY__EXTERN__MODULE, _2438_externUseDecls))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
      }
      DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _2443_allModules;
      _2443_allModules = DafnyCompilerRustUtils.SeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Empty();
      BigInteger _hi56 = new BigInteger((p).Count);
      for (BigInteger _2444_i = BigInteger.Zero; _2444_i < _hi56; _2444_i++) {
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _2445_m;
        DafnyCompilerRustUtils._ISeqMap<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule> _out687;
        _out687 = (this).GenModule((p).Select(_2444_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2445_m = _out687;
        _2443_allModules = DafnyCompilerRustUtils.GatheringModule.MergeSeqMap(_2443_allModules, _2445_m);
      }
      BigInteger _hi57 = new BigInteger(((_2443_allModules).dtor_keys).Count);
      for (BigInteger _2446_i = BigInteger.Zero; _2446_i < _hi57; _2446_i++) {
        if (!((_2443_allModules).dtor_values).Contains(((_2443_allModules).dtor_keys).Select(_2446_i))) {
          goto continue_0;
        }
        RAST._IMod _2447_m;
        _2447_m = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, DafnyCompilerRustUtils._IGatheringModule>.Select((_2443_allModules).dtor_values,((_2443_allModules).dtor_keys).Select(_2446_i))).ToRust();
        BigInteger _hi58 = new BigInteger((this.optimizations).Count);
        for (BigInteger _2448_j = BigInteger.Zero; _2448_j < _hi58; _2448_j++) {
          _2447_m = Dafny.Helpers.Id<Func<RAST._IMod, RAST._IMod>>((this.optimizations).Select(_2448_j))(_2447_m);
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (_2447_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      continue_0: ;
      }
    after_0: ;
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2449_i;
      _2449_i = BigInteger.Zero;
      while ((_2449_i) < (new BigInteger((fullName).Count))) {
        if ((_2449_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2449_i)));
        _2449_i = (_2449_i) + (BigInteger.One);
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