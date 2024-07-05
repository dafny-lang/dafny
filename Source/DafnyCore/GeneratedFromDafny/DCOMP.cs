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
      Dafny.ISequence<Dafny.Rune> _1138___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1138___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1138___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1138___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(new BigInteger(2));
        i = _in124;
        goto TAIL_CALL_START;
      } else {
        _1138___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1138___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1139___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1139___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1139___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1139___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in126 = (i).Drop(BigInteger.One);
        i = _in126;
        goto TAIL_CALL_START;
      } else {
        _1139___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1139___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1140_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1140_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeVar(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1141_r = (f);
      if ((DCOMP.__default.reserved__vars).Contains(_1141_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1141_r);
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
      var _pat_let_tv137 = dafnyName;
      var _pat_let_tv138 = rs;
      var _pat_let_tv139 = dafnyName;
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _1142_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source54 = (rs).Select(BigInteger.Zero);
          bool unmatched54 = true;
          if (unmatched54) {
            if (_source54.is_UserDefined) {
              DAST._IResolvedType _1143_resolvedType = _source54.dtor_resolved;
              unmatched54 = false;
              return DCOMP.__default.TraitTypeContainingMethod(_1143_resolvedType, _pat_let_tv137);
            }
          }
          if (unmatched54) {
            unmatched54 = false;
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
          throw new System.Exception("unexpected control point");
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source55 = _1142_res;
        bool unmatched55 = true;
        if (unmatched55) {
          if (_source55.is_Some) {
            unmatched55 = false;
            return _1142_res;
          }
        }
        if (unmatched55) {
          unmatched55 = false;
          return DCOMP.__default.TraitTypeContainingMethodAux((_pat_let_tv138).Drop(BigInteger.One), _pat_let_tv139);
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
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _source56 = _1152_attr;
        bool unmatched56 = true;
        if (unmatched56) {
          if (_source56.is_Some) {
            DCOMP._IExternAttribute _1153_n = _source56.dtor_value;
            unmatched56 = false;
            res = _1153_n;
            return res;
          }
        }
        if (unmatched56) {
          unmatched56 = false;
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
      _1158_modName = DCOMP.__default.escapeName((mod).dtor_name);
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
            _1160_body = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (((RAST.__default.crate).MSel(DCOMP.COMP.DAFNY__EXTERN__MODULE)).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1159_optExtern).dtor_overrideName))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))), _1160_body);
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
        DAST._IModuleItem _source57 = (body).Select(_1161_i);
        bool unmatched57 = true;
        if (unmatched57) {
          if (_source57.is_Module) {
            DAST._IModule _1163_m = _source57.dtor_Module_a0;
            unmatched57 = false;
            RAST._IMod _1164_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1163_m, containingPath);
            _1164_mm = _out16;
            _1162_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1164_mm));
          }
        }
        if (unmatched57) {
          if (_source57.is_Class) {
            DAST._IClass _1165_c = _source57.dtor_Class_a0;
            unmatched57 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1165_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1165_c).dtor_name)));
            _1162_generated = _out17;
          }
        }
        if (unmatched57) {
          if (_source57.is_Trait) {
            DAST._ITrait _1166_t = _source57.dtor_Trait_a0;
            unmatched57 = false;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenTrait(_1166_t, containingPath);
            _1162_generated = _out18;
          }
        }
        if (unmatched57) {
          if (_source57.is_Newtype) {
            DAST._INewtype _1167_n = _source57.dtor_Newtype_a0;
            unmatched57 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1167_n);
            _1162_generated = _out19;
          }
        }
        if (unmatched57) {
          if (_source57.is_SynonymType) {
            DAST._ISynonymType _1168_s = _source57.dtor_SynonymType_a0;
            unmatched57 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1168_s);
            _1162_generated = _out20;
          }
        }
        if (unmatched57) {
          DAST._IDatatype _1169_d = _source57.dtor_Datatype_a0;
          unmatched57 = false;
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
        _1170_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1170_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1170_genTpConstraint);
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
        _1186_fieldRustName = DCOMP.__default.escapeVar(((_1184_field).dtor_formal).dtor_name);
        _1181_fields = Dafny.Sequence<RAST._IField>.Concat(_1181_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1186_fieldRustName, _1185_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source58 = (_1184_field).dtor_defaultValue;
        bool unmatched58 = true;
        if (unmatched58) {
          if (_source58.is_Some) {
            DAST._IExpression _1187_e = _source58.dtor_value;
            unmatched58 = false;
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
        if (unmatched58) {
          unmatched58 = false;
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
        _1181_fields = Dafny.Sequence<RAST._IField>.Concat(_1181_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1192_typeParamI)), RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1195_rTypeArg))))));
        _1182_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1182_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1192_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      DCOMP._IExternAttribute _1196_extern;
      _1196_extern = DCOMP.__default.ExtractExtern((c).dtor_attributes, (c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _1197_className = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((_1196_extern).is_SimpleExtern) {
        _1197_className = (_1196_extern).dtor_overrideName;
      } else {
        _1197_className = DCOMP.__default.escapeName((c).dtor_name);
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
        _1199_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.__default.SelfOwned)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel((this).allocate)).AsExpr()).ApplyType1(RAST.__default.SelfOwned)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1199_implBody);
      }
      RAST._IType _1201_selfTypeForImpl = RAST.Type.Default();
      if (((_1196_extern).is_NoExtern) || ((_1196_extern).is_UnsupportedExtern)) {
        _1201_selfTypeForImpl = RAST.Type.create_TIdentifier(_1197_className);
      } else if ((_1196_extern).is_AdvancedExtern) {
        _1201_selfTypeForImpl = (((RAST.__default.crate).MSel((_1196_extern).dtor_enclosingModule)).MSel((_1196_extern).dtor_overrideName)).AsType();
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
      _out38 = DCOMP.COMP.GenPathType(path);
      _1203_genSelfPath = _out38;
      if (!(_1197_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1178_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(RAST.__default.AnyTrait))), RAST.Type.create_TypeApp(_1203_genSelfPath, _1177_rTypeParams), _1179_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(RAST.__default.AnyTrait)))))))));
      }
      Dafny.ISequence<DAST._IType> _1204_superClasses;
      _1204_superClasses = (((_1197_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) ? (Dafny.Sequence<DAST._IType>.FromElements()) : ((c).dtor_superClasses));
      BigInteger _hi10 = new BigInteger((_1204_superClasses).Count);
      for (BigInteger _1205_i = BigInteger.Zero; _1205_i < _hi10; _1205_i++) {
        DAST._IType _1206_superClass;
        _1206_superClass = (_1204_superClasses).Select(_1205_i);
        DAST._IType _source59 = _1206_superClass;
        bool unmatched59 = true;
        if (unmatched59) {
          if (_source59.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source59.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1207_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1208_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1209_properMethods = resolved0.dtor_properMethods;
              unmatched59 = false;
              {
                RAST._IType _1210_pathStr;
                RAST._IType _out39;
                _out39 = DCOMP.COMP.GenPathType(_1207_traitPath);
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
  return (_1215_s);
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")  bodiless and mark as {:extern} and implement them in a Rust file, ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("or mark none of them as {:extern} and implement them in Dafny. ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.")));
                  }
                }
                RAST._IModDecl _1216_x;
                _1216_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1178_rTypeParamsDecls, _1213_traitType, RAST.Type.create_TypeApp(_1203_genSelfPath, _1177_rTypeParams), _1179_whereConstraints, _1212_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1216_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1178_rTypeParamsDecls, (((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1213_traitType))), RAST.Type.create_TypeApp(_1203_genSelfPath, _1177_rTypeParams), _1179_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro((((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).AsExpr()).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1213_traitType)))))))));
              }
            }
          }
        }
        if (unmatched59) {
          unmatched59 = false;
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
        _1228_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1228_parents, Dafny.Sequence<RAST._IType>.FromElements(_1230_tpe)), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.dafny__runtime).MSel((this).Upcast)).AsType()).Apply1(RAST.Type.create_DynType(_1230_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1218_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1219_typeParams), _1228_parents, _1226_implBody)));
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
      Std.Wrappers._IOption<RAST._IType> _source60 = DCOMP.COMP.NewtypeRangeToRustType((c).dtor_range);
      bool unmatched60 = true;
      if (unmatched60) {
        if (_source60.is_Some) {
          RAST._IType _1237_v = _source60.dtor_value;
          unmatched60 = false;
          _1236_underlyingType = _1237_v;
        }
      }
      if (unmatched60) {
        unmatched60 = false;
        RAST._IType _out51;
        _out51 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1236_underlyingType = _out51;
      }
      DAST._IType _1238_resultingType;
      _1238_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1239_newtypeName;
      _1239_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1239_newtypeName, _1233_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1236_underlyingType))))));
      RAST._IExpr _1240_fnBody;
      _1240_fnBody = RAST.Expr.create_Identifier(_1239_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source61 = (c).dtor_witnessExpr;
      bool unmatched61 = true;
      if (unmatched61) {
        if (_source61.is_Some) {
          DAST._IExpression _1241_e = _source61.dtor_value;
          unmatched61 = false;
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
      if (unmatched61) {
        unmatched61 = false;
        {
          _1240_fnBody = (_1240_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1246_body;
      _1246_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1240_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source62 = (c).dtor_constraint;
      bool unmatched62 = true;
      if (unmatched62) {
        if (_source62.is_None) {
          unmatched62 = false;
        }
      }
      if (unmatched62) {
        DAST._INewtypeConstraint value8 = _source62.dtor_value;
        DAST._IFormal _1247_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1248_constraintStmts = value8.dtor_constraintStmts;
        unmatched62 = false;
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
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1233_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1239_newtypeName), _1232_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1236_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(((RAST.Path.create_Self()).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))).AsType())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
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
      _1257_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1258_resultingType;
      RAST._IType _out63;
      _out63 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1258_resultingType = _out63;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1257_synonymTypeName, _1255_rTypeParamsDecls, _1258_resultingType)));
      Dafny.ISequence<RAST._ITypeParamDecl> _1259_defaultConstrainedTypeParams;
      _1259_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1255_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Std.Wrappers._IOption<DAST._IExpression> _source63 = (c).dtor_witnessExpr;
      bool unmatched63 = true;
      if (unmatched63) {
        if (_source63.is_Some) {
          DAST._IExpression _1260_e = _source63.dtor_value;
          unmatched63 = false;
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
      if (unmatched63) {
        unmatched63 = false;
      }
      return s;
    }
    public bool TypeIsEq(DAST._IType t) {
      DAST._IType _source64 = t;
      bool unmatched64 = true;
      if (unmatched64) {
        if (_source64.is_UserDefined) {
          unmatched64 = false;
          return true;
        }
      }
      if (unmatched64) {
        if (_source64.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1268_ts = _source64.dtor_Tuple_a0;
          unmatched64 = false;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1269_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1269_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1270_t = (DAST._IType)_forall_var_5;
            return !((_1269_ts).Contains(_1270_t)) || ((this).TypeIsEq(_1270_t));
          }))))(_1268_ts);
        }
      }
      if (unmatched64) {
        if (_source64.is_Array) {
          DAST._IType _1271_t = _source64.dtor_element;
          unmatched64 = false;
          return (this).TypeIsEq(_1271_t);
        }
      }
      if (unmatched64) {
        if (_source64.is_Seq) {
          DAST._IType _1272_t = _source64.dtor_element;
          unmatched64 = false;
          return (this).TypeIsEq(_1272_t);
        }
      }
      if (unmatched64) {
        if (_source64.is_Set) {
          DAST._IType _1273_t = _source64.dtor_element;
          unmatched64 = false;
          return (this).TypeIsEq(_1273_t);
        }
      }
      if (unmatched64) {
        if (_source64.is_Multiset) {
          DAST._IType _1274_t = _source64.dtor_element;
          unmatched64 = false;
          return (this).TypeIsEq(_1274_t);
        }
      }
      if (unmatched64) {
        if (_source64.is_Map) {
          DAST._IType _1275_k = _source64.dtor_key;
          DAST._IType _1276_v = _source64.dtor_value;
          unmatched64 = false;
          return ((this).TypeIsEq(_1275_k)) && ((this).TypeIsEq(_1276_v));
        }
      }
      if (unmatched64) {
        if (_source64.is_SetBuilder) {
          DAST._IType _1277_t = _source64.dtor_element;
          unmatched64 = false;
          return (this).TypeIsEq(_1277_t);
        }
      }
      if (unmatched64) {
        if (_source64.is_MapBuilder) {
          DAST._IType _1278_k = _source64.dtor_key;
          DAST._IType _1279_v = _source64.dtor_value;
          unmatched64 = false;
          return ((this).TypeIsEq(_1278_k)) && ((this).TypeIsEq(_1279_v));
        }
      }
      if (unmatched64) {
        if (_source64.is_Arrow) {
          unmatched64 = false;
          return false;
        }
      }
      if (unmatched64) {
        if (_source64.is_Primitive) {
          unmatched64 = false;
          return true;
        }
      }
      if (unmatched64) {
        if (_source64.is_Passthrough) {
          unmatched64 = false;
          return true;
        }
      }
      if (unmatched64) {
        if (_source64.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _1280_i = _source64.dtor_TypeArg_a0;
          unmatched64 = false;
          return true;
        }
      }
      if (unmatched64) {
        unmatched64 = false;
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
      _1288_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
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
          _1299_formalName = DCOMP.__default.escapeVar(((_1297_dtor).dtor_formal).dtor_name);
          if (((_1296_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1299_formalName))) {
            _1295_isNumeric = true;
          }
          if ((((_1296_j).Sign != 0) && (_1295_isNumeric)) && (!(Std.Strings.__default.OfNat(_1296_j)).Equals(_1299_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1299_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1296_j)));
            _1295_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1294_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1294_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1299_formalName, RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1298_formalType))))));
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
          _1310_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1309_dtor).dtor_callName, DCOMP.__default.escapeVar(((_1309_dtor).dtor_formal).dtor_name));
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
                _1322_patternName = DCOMP.__default.escapeVar(((_1321_dtor2).dtor_formal).dtor_name);
                if (((_1320_l).Sign == 0) && ((_1322_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1319_isNumeric = true;
                }
                if (_1319_isNumeric) {
                  _1322_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1321_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1320_l)));
                }
                if (object.Equals(((_1309_dtor).dtor_formal).dtor_name, ((_1321_dtor2).dtor_formal).dtor_name)) {
                  _1317_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1322_patternName);
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
              RAST._IMatchCase _1323_ctorMatch;
              _1323_ctorMatch = RAST.MatchCase.create(_1315_pattern, RAST.Expr.create_RawExpr(_1316_rhs));
              _1312_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1312_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1323_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1312_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1312_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1288_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _1324_methodBody;
            _1324_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1312_cases);
            _1304_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1304_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1310_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1311_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1324_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1325_coerceTypes;
      _1325_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1326_rCoerceTypeParams;
      _1326_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1327_coerceArguments;
      _1327_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1328_coerceMap;
      _1328_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1329_rCoerceMap;
      _1329_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1330_coerceMapToArg;
      _1330_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1331_types;
        _1331_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi19 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1332_typeI = BigInteger.Zero; _1332_typeI < _hi19; _1332_typeI++) {
          DAST._ITypeArgDecl _1333_typeParam;
          _1333_typeParam = ((c).dtor_typeParams).Select(_1332_typeI);
          DAST._IType _1334_typeArg;
          RAST._ITypeParamDecl _1335_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(_1333_typeParam, out _out78, out _out79);
          _1334_typeArg = _out78;
          _1335_rTypeParamDecl = _out79;
          RAST._IType _1336_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1334_typeArg, DCOMP.GenTypeContext.@default());
          _1336_rTypeArg = _out80;
          _1331_types = Dafny.Sequence<RAST._IType>.Concat(_1331_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1336_rTypeArg))));
          if (((_1332_typeI) < (new BigInteger((_1290_variances).Count))) && (((_1290_variances).Select(_1332_typeI)).is_Nonvariant)) {
            _1325_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1325_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1336_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1337_coerceTypeParam;
          _1337_coerceTypeParam = Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_1333_typeParam, _pat_let9_0 => Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_pat_let9_0, _1338_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1332_typeI)), _pat_let10_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(_pat_let10_0, _1339_dt__update_hname_h0 => DAST.TypeArgDecl.create(_1339_dt__update_hname_h0, (_1338_dt__update__tmp_h0).dtor_bounds, (_1338_dt__update__tmp_h0).dtor_variance)))));
          DAST._IType _1340_coerceTypeArg;
          RAST._ITypeParamDecl _1341_rCoerceTypeParamDecl;
          DAST._IType _out81;
          RAST._ITypeParamDecl _out82;
          (this).GenTypeParam(_1337_coerceTypeParam, out _out81, out _out82);
          _1340_coerceTypeArg = _out81;
          _1341_rCoerceTypeParamDecl = _out82;
          _1328_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1328_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1334_typeArg, _1340_coerceTypeArg)));
          RAST._IType _1342_rCoerceType;
          RAST._IType _out83;
          _out83 = (this).GenType(_1340_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1342_rCoerceType = _out83;
          _1329_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1329_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1336_rTypeArg, _1342_rCoerceType)));
          _1325_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1325_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1342_rCoerceType));
          _1326_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1326_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1341_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1343_coerceFormal;
          _1343_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1332_typeI));
          _1330_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1330_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1336_rTypeArg, _1342_rCoerceType), (RAST.Expr.create_Identifier(_1343_coerceFormal)).Clone())));
          _1327_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1327_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1343_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1336_rTypeArg), _1342_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        _1289_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1289_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1344_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1344_tpe);
})), _1331_types)))));
      }
      bool _1345_cIsEq;
      _1345_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1345_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1288_datatypeName, _1286_rTypeParamsDecls, _1289_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1286_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams), _1287_whereConstraints, _1304_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1346_printImplBodyCases;
      _1346_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1347_hashImplBodyCases;
      _1347_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1348_coerceImplBodyCases;
      _1348_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi20 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1349_i = BigInteger.Zero; _1349_i < _hi20; _1349_i++) {
        DAST._IDatatypeCtor _1350_ctor;
        _1350_ctor = ((c).dtor_ctors).Select(_1349_i);
        Dafny.ISequence<Dafny.Rune> _1351_ctorMatch;
        _1351_ctorMatch = DCOMP.__default.escapeName((_1350_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1352_modulePrefix;
        _1352_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1353_ctorName;
        _1353_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1352_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1350_ctor).dtor_name));
        if (((new BigInteger((_1353_ctorName).Count)) >= (new BigInteger(13))) && (((_1353_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1353_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1354_printRhs;
        _1354_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1353_ctorName), (((_1350_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1355_hashRhs;
        _1355_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1356_coerceRhsArgs;
        _1356_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1357_isNumeric;
        _1357_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1358_ctorMatchInner;
        _1358_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi21 = new BigInteger(((_1350_ctor).dtor_args).Count);
        for (BigInteger _1359_j = BigInteger.Zero; _1359_j < _hi21; _1359_j++) {
          DAST._IDatatypeDtor _1360_dtor;
          _1360_dtor = ((_1350_ctor).dtor_args).Select(_1359_j);
          Dafny.ISequence<Dafny.Rune> _1361_patternName;
          _1361_patternName = DCOMP.__default.escapeVar(((_1360_dtor).dtor_formal).dtor_name);
          DAST._IType _1362_formalType;
          _1362_formalType = ((_1360_dtor).dtor_formal).dtor_typ;
          if (((_1359_j).Sign == 0) && ((_1361_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1357_isNumeric = true;
          }
          if (_1357_isNumeric) {
            _1361_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1360_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1359_j)));
          }
          _1355_hashRhs = (((_1362_formalType).is_Arrow) ? ((_1355_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))) : ((_1355_hashRhs).Then((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1361_patternName), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state")))))));
          _1358_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1358_ctorMatchInner, _1361_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1359_j).Sign == 1) {
            _1354_printRhs = (_1354_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1354_printRhs = (_1354_printRhs).Then(RAST.Expr.create_RawExpr((((_1362_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1361_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1363_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1364_formalTpe;
          RAST._IType _out84;
          _out84 = (this).GenType(_1362_formalType, DCOMP.GenTypeContext.@default());
          _1364_formalTpe = _out84;
          DAST._IType _1365_newFormalType;
          _1365_newFormalType = (_1362_formalType).Replace(_1328_coerceMap);
          RAST._IType _1366_newFormalTpe;
          _1366_newFormalTpe = (_1364_formalTpe).Replace(_1329_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1367_upcastConverter;
          _1367_upcastConverter = (this).UpcastConversionLambda(_1362_formalType, _1364_formalTpe, _1365_newFormalType, _1366_newFormalTpe, _1330_coerceMapToArg);
          if ((_1367_upcastConverter).is_Success) {
            RAST._IExpr _1368_coercionFunction;
            _1368_coercionFunction = (_1367_upcastConverter).dtor_value;
            _1363_coerceRhsArg = (_1368_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1361_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1359_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1288_datatypeName));
            _1363_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1356_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1356_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1361_patternName, _1363_coerceRhsArg)));
        }
        RAST._IExpr _1369_coerceRhs;
        _1369_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1288_datatypeName)).FSel(DCOMP.__default.escapeName((_1350_ctor).dtor_name)), _1356_coerceRhsArgs);
        if (_1357_isNumeric) {
          _1351_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1351_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1358_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1351_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1351_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1358_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1350_ctor).dtor_hasAnyArgs) {
          _1354_printRhs = (_1354_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1354_printRhs = (_1354_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1346_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1346_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1288_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1351_ctorMatch), RAST.Expr.create_Block(_1354_printRhs))));
        _1347_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1347_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1288_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1351_ctorMatch), RAST.Expr.create_Block(_1355_hashRhs))));
        _1348_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1348_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1288_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1351_ctorMatch), RAST.Expr.create_Block(_1369_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1370_extraCases;
        _1370_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1288_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _1346_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1346_printImplBodyCases, _1370_extraCases);
        _1347_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1347_hashImplBodyCases, _1370_extraCases);
        _1348_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1348_coerceImplBodyCases, _1370_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1371_defaultConstrainedTypeParams;
      _1371_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1286_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1372_rTypeParamsDeclsWithEq;
      _1372_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1286_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1373_rTypeParamsDeclsWithHash;
      _1373_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1286_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1374_printImplBody;
      _1374_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1346_printImplBodyCases);
      RAST._IExpr _1375_hashImplBody;
      _1375_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1347_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1286_rTypeParamsDecls, (((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug"))).AsType(), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType()))), Std.Wrappers.Option<RAST._IType>.create_Some((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Result"))).AsType()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1286_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))).AsType())), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1374_printImplBody))))))));
      if ((new BigInteger((_1326_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1376_coerceImplBody;
        _1376_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1348_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1286_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1326_rCoerceTypeParams, _1327_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1325_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.__default.SelfOwned)), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1325_coerceTypes)), _1376_coerceImplBody))))))))));
      }
      if (_1345_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1372_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1373_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))).AsType()))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1375_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1377_structName;
        _1377_structName = (RAST.Expr.create_Identifier(_1288_datatypeName)).FSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1378_structAssignments;
        _1378_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi22 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1379_i = BigInteger.Zero; _1379_i < _hi22; _1379_i++) {
          DAST._IDatatypeDtor _1380_dtor;
          _1380_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1379_i);
          _1378_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1378_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(((_1380_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1381_defaultConstrainedTypeParams;
        _1381_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1286_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1382_fullType;
        _1382_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1288_datatypeName), _1285_rTypeParams);
        if (_1345_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1381_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1382_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1382_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1377_structName, _1378_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1286_rTypeParamsDecls, ((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).AsType()).Apply1(_1382_fullType), RAST.Type.create_Borrowed(_1382_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.SelfOwned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        for (BigInteger _1383_i = BigInteger.Zero; _1383_i < _hi23; _1383_i++) {
          Dafny.ISequence<Dafny.Rune> _1384_id;
          _1384_id = ((p).Select(_1383_i));
          r = (r).MSel(((escape) ? (DCOMP.__default.escapeName(_1384_id)) : (DCOMP.__default.ReplaceDotByDoubleColon((_1384_id)))));
        }
      }
      return r;
    }
    public static RAST._IType GenPathType(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IType t = RAST.Type.Default();
      RAST._IPath _1385_p;
      RAST._IPath _out85;
      _out85 = DCOMP.COMP.GenPath(p, true);
      _1385_p = _out85;
      t = (_1385_p).AsType();
      return t;
    }
    public static RAST._IExpr GenPathExpr(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p, bool escape)
    {
      RAST._IExpr e = RAST.Expr.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        e = RAST.__default.self;
        return e;
      }
      RAST._IPath _1386_p;
      RAST._IPath _out86;
      _out86 = DCOMP.COMP.GenPath(p, escape);
      _1386_p = _out86;
      e = (_1386_p).AsExpr();
      return e;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi24 = new BigInteger((args).Count);
      for (BigInteger _1387_i = BigInteger.Zero; _1387_i < _hi24; _1387_i++) {
        RAST._IType _1388_genTp;
        RAST._IType _out87;
        _out87 = (this).GenType((args).Select(_1387_i), genTypeContext);
        _1388_genTp = _out87;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1388_genTp));
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, DCOMP._IGenTypeContext genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source65 = c;
      bool unmatched65 = true;
      if (unmatched65) {
        if (_source65.is_UserDefined) {
          DAST._IResolvedType _1389_resolved = _source65.dtor_resolved;
          unmatched65 = false;
          {
            RAST._IType _1390_t;
            RAST._IType _out88;
            _out88 = DCOMP.COMP.GenPathType((_1389_resolved).dtor_path);
            _1390_t = _out88;
            Dafny.ISequence<RAST._IType> _1391_typeArgs;
            Dafny.ISequence<RAST._IType> _out89;
            _out89 = (this).GenTypeArgs((_1389_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _1392_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _1393_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1392_dt__update__tmp_h0).dtor_inBinding, (_1392_dt__update__tmp_h0).dtor_inFn, _1393_dt__update_hforTraitParents_h0))))));
            _1391_typeArgs = _out89;
            s = RAST.Type.create_TypeApp(_1390_t, _1391_typeArgs);
            DAST._IResolvedTypeBase _source66 = (_1389_resolved).dtor_kind;
            bool unmatched66 = true;
            if (unmatched66) {
              if (_source66.is_Class) {
                unmatched66 = false;
                {
                  s = (this).Object(s);
                }
              }
            }
            if (unmatched66) {
              if (_source66.is_Datatype) {
                unmatched66 = false;
                {
                  if ((this).IsRcWrapped((_1389_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched66) {
              if (_source66.is_Trait) {
                unmatched66 = false;
                {
                  if (((_1389_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = RAST.__default.AnyTrait;
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched66) {
              DAST._IType _1394_base = _source66.dtor_baseType;
              DAST._INewtypeRange _1395_range = _source66.dtor_range;
              bool _1396_erased = _source66.dtor_erase;
              unmatched66 = false;
              {
                if (_1396_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source67 = DCOMP.COMP.NewtypeRangeToRustType(_1395_range);
                  bool unmatched67 = true;
                  if (unmatched67) {
                    if (_source67.is_Some) {
                      RAST._IType _1397_v = _source67.dtor_value;
                      unmatched67 = false;
                      s = _1397_v;
                    }
                  }
                  if (unmatched67) {
                    unmatched67 = false;
                    RAST._IType _1398_underlying;
                    RAST._IType _out90;
                    _out90 = (this).GenType(_1394_base, DCOMP.GenTypeContext.@default());
                    _1398_underlying = _out90;
                    s = RAST.Type.create_TSynonym(s, _1398_underlying);
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Object) {
          unmatched65 = false;
          {
            s = RAST.__default.AnyTrait;
            if (!((genTypeContext).dtor_forTraitParents)) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1399_types = _source65.dtor_Tuple_a0;
          unmatched65 = false;
          {
            Dafny.ISequence<RAST._IType> _1400_args;
            _1400_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1401_i;
            _1401_i = BigInteger.Zero;
            while ((_1401_i) < (new BigInteger((_1399_types).Count))) {
              RAST._IType _1402_generated;
              RAST._IType _out91;
              _out91 = (this).GenType((_1399_types).Select(_1401_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _1403_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _1404_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1403_dt__update__tmp_h1).dtor_inBinding, (_1403_dt__update__tmp_h1).dtor_inFn, _1404_dt__update_hforTraitParents_h1))))));
              _1402_generated = _out91;
              _1400_args = Dafny.Sequence<RAST._IType>.Concat(_1400_args, Dafny.Sequence<RAST._IType>.FromElements(_1402_generated));
              _1401_i = (_1401_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1399_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1400_args)) : (RAST.__default.SystemTupleType(_1400_args)));
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Array) {
          DAST._IType _1405_element = _source65.dtor_element;
          BigInteger _1406_dims = _source65.dtor_dims;
          unmatched65 = false;
          {
            if ((_1406_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1407_elem;
              RAST._IType _out92;
              _out92 = (this).GenType(_1405_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _1408_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _1409_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1408_dt__update__tmp_h2).dtor_inBinding, (_1408_dt__update__tmp_h2).dtor_inFn, _1409_dt__update_hforTraitParents_h2))))));
              _1407_elem = _out92;
              if ((_1406_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1407_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1410_n;
                _1410_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1406_dims));
                s = (((RAST.__default.dafny__runtime).MSel(_1410_n)).AsType()).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1407_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Seq) {
          DAST._IType _1411_element = _source65.dtor_element;
          unmatched65 = false;
          {
            RAST._IType _1412_elem;
            RAST._IType _out93;
            _out93 = (this).GenType(_1411_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _1413_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _1414_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1413_dt__update__tmp_h3).dtor_inBinding, (_1413_dt__update__tmp_h3).dtor_inFn, _1414_dt__update_hforTraitParents_h3))))));
            _1412_elem = _out93;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1412_elem));
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Set) {
          DAST._IType _1415_element = _source65.dtor_element;
          unmatched65 = false;
          {
            RAST._IType _1416_elem;
            RAST._IType _out94;
            _out94 = (this).GenType(_1415_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _1417_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _1418_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1417_dt__update__tmp_h4).dtor_inBinding, (_1417_dt__update__tmp_h4).dtor_inFn, _1418_dt__update_hforTraitParents_h4))))));
            _1416_elem = _out94;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1416_elem));
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Multiset) {
          DAST._IType _1419_element = _source65.dtor_element;
          unmatched65 = false;
          {
            RAST._IType _1420_elem;
            RAST._IType _out95;
            _out95 = (this).GenType(_1419_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _1421_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _1422_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1421_dt__update__tmp_h5).dtor_inBinding, (_1421_dt__update__tmp_h5).dtor_inFn, _1422_dt__update_hforTraitParents_h5))))));
            _1420_elem = _out95;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1420_elem));
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Map) {
          DAST._IType _1423_key = _source65.dtor_key;
          DAST._IType _1424_value = _source65.dtor_value;
          unmatched65 = false;
          {
            RAST._IType _1425_keyType;
            RAST._IType _out96;
            _out96 = (this).GenType(_1423_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _1426_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _1427_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1426_dt__update__tmp_h6).dtor_inBinding, (_1426_dt__update__tmp_h6).dtor_inFn, _1427_dt__update_hforTraitParents_h6))))));
            _1425_keyType = _out96;
            RAST._IType _1428_valueType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1424_value, genTypeContext);
            _1428_valueType = _out97;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1425_keyType, _1428_valueType));
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_MapBuilder) {
          DAST._IType _1429_key = _source65.dtor_key;
          DAST._IType _1430_value = _source65.dtor_value;
          unmatched65 = false;
          {
            RAST._IType _1431_keyType;
            RAST._IType _out98;
            _out98 = (this).GenType(_1429_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _1432_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _1433_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1432_dt__update__tmp_h7).dtor_inBinding, (_1432_dt__update__tmp_h7).dtor_inFn, _1433_dt__update_hforTraitParents_h7))))));
            _1431_keyType = _out98;
            RAST._IType _1434_valueType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1430_value, genTypeContext);
            _1434_valueType = _out99;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1431_keyType, _1434_valueType));
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_SetBuilder) {
          DAST._IType _1435_elem = _source65.dtor_element;
          unmatched65 = false;
          {
            RAST._IType _1436_elemType;
            RAST._IType _out100;
            _out100 = (this).GenType(_1435_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _1437_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _1438_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1437_dt__update__tmp_h8).dtor_inBinding, (_1437_dt__update__tmp_h8).dtor_inFn, _1438_dt__update_hforTraitParents_h8))))));
            _1436_elemType = _out100;
            s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(_1436_elemType));
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1439_args = _source65.dtor_args;
          DAST._IType _1440_result = _source65.dtor_result;
          unmatched65 = false;
          {
            Dafny.ISequence<RAST._IType> _1441_argTypes;
            _1441_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1442_i;
            _1442_i = BigInteger.Zero;
            while ((_1442_i) < (new BigInteger((_1439_args).Count))) {
              RAST._IType _1443_generated;
              RAST._IType _out101;
              _out101 = (this).GenType((_1439_args).Select(_1442_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let29_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let29_0, _1444_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let30_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let30_0, _1445_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let31_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let31_0, _1446_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1444_dt__update__tmp_h9).dtor_inBinding, _1446_dt__update_hinFn_h0, _1445_dt__update_hforTraitParents_h9))))))));
              _1443_generated = _out101;
              _1441_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1441_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1443_generated)));
              _1442_i = (_1442_i) + (BigInteger.One);
            }
            RAST._IType _1447_resultType;
            RAST._IType _out102;
            _out102 = (this).GenType(_1440_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1447_resultType = _out102;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1441_argTypes, _1447_resultType)));
          }
        }
      }
      if (unmatched65) {
        if (_source65.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source65.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1448_name = _h90;
          unmatched65 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1448_name));
        }
      }
      if (unmatched65) {
        if (_source65.is_Primitive) {
          DAST._IPrimitive _1449_p = _source65.dtor_Primitive_a0;
          unmatched65 = false;
          {
            DAST._IPrimitive _source68 = _1449_p;
            bool unmatched68 = true;
            if (unmatched68) {
              if (_source68.is_Int) {
                unmatched68 = false;
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"))).AsType();
              }
            }
            if (unmatched68) {
              if (_source68.is_Real) {
                unmatched68 = false;
                s = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"))).AsType();
              }
            }
            if (unmatched68) {
              if (_source68.is_String) {
                unmatched68 = false;
                s = RAST.Type.create_TypeApp(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType(), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType()));
              }
            }
            if (unmatched68) {
              if (_source68.is_Bool) {
                unmatched68 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched68) {
              unmatched68 = false;
              s = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsType();
            }
          }
        }
      }
      if (unmatched65) {
        Dafny.ISequence<Dafny.Rune> _1450_v = _source65.dtor_Passthrough_a0;
        unmatched65 = false;
        s = RAST.__default.RawType(_1450_v);
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
      for (BigInteger _1451_i = BigInteger.Zero; _1451_i < _hi25; _1451_i++) {
        DAST._IMethod _source69 = (body).Select(_1451_i);
        bool unmatched69 = true;
        if (unmatched69) {
          DAST._IMethod _1452_m = _source69;
          unmatched69 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source70 = (_1452_m).dtor_overridingPath;
            bool unmatched70 = true;
            if (unmatched70) {
              if (_source70.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1453_p = _source70.dtor_value;
                unmatched70 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1454_existing;
                  _1454_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1453_p)) {
                    _1454_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1453_p);
                  }
                  if (((new BigInteger(((_1452_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1455_genMethod;
                  RAST._IImplMember _out103;
                  _out103 = (this).GenMethod(_1452_m, true, enclosingType, enclosingTypeParams);
                  _1455_genMethod = _out103;
                  _1454_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1454_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1455_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1453_p, _1454_existing)));
                }
              }
            }
            if (unmatched70) {
              unmatched70 = false;
              {
                RAST._IImplMember _1456_generated;
                RAST._IImplMember _out104;
                _out104 = (this).GenMethod(_1452_m, forTrait, enclosingType, enclosingTypeParams);
                _1456_generated = _out104;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1456_generated));
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
      for (BigInteger _1457_i = BigInteger.Zero; _1457_i < _hi26; _1457_i++) {
        DAST._IFormal _1458_param;
        _1458_param = (@params).Select(_1457_i);
        RAST._IType _1459_paramType;
        RAST._IType _out105;
        _out105 = (this).GenType((_1458_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1459_paramType = _out105;
        if (((!((_1459_paramType).CanReadWithoutClone())) || (forLambda)) && (!((_1458_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1459_paramType = RAST.Type.create_Borrowed(_1459_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeVar((_1458_param).dtor_name), _1459_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1460_params;
      Dafny.ISequence<RAST._IFormal> _out106;
      _out106 = (this).GenParams((m).dtor_params, false);
      _1460_params = _out106;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1461_paramNames;
      _1461_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1462_paramTypes;
      _1462_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi27 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1463_paramI = BigInteger.Zero; _1463_paramI < _hi27; _1463_paramI++) {
        DAST._IFormal _1464_dafny__formal;
        _1464_dafny__formal = ((m).dtor_params).Select(_1463_paramI);
        RAST._IFormal _1465_formal;
        _1465_formal = (_1460_params).Select(_1463_paramI);
        Dafny.ISequence<Dafny.Rune> _1466_name;
        _1466_name = (_1465_formal).dtor_name;
        _1461_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1461_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1466_name));
        _1462_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1462_paramTypes, _1466_name, (_1465_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1467_fnName;
      _1467_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1468_selfIdent;
      _1468_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1469_selfId;
        _1469_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1469_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv140 = enclosingTypeParams;
        var _pat_let_tv141 = enclosingType;
        DAST._IType _1470_instanceType;
        _1470_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source71 = enclosingType;
          bool unmatched71 = true;
          if (unmatched71) {
            if (_source71.is_UserDefined) {
              DAST._IResolvedType _1471_r = _source71.dtor_resolved;
              unmatched71 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1471_r, _pat_let32_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let32_0, _1472_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv140, _pat_let33_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let33_0, _1473_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1472_dt__update__tmp_h0).dtor_path, _1473_dt__update_htypeArgs_h0, (_1472_dt__update__tmp_h0).dtor_kind, (_1472_dt__update__tmp_h0).dtor_attributes, (_1472_dt__update__tmp_h0).dtor_properMethods, (_1472_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched71) {
            unmatched71 = false;
            return _pat_let_tv141;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1474_selfFormal;
          _1474_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1460_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1474_selfFormal), _1460_params);
        } else {
          RAST._IType _1475_tpe;
          RAST._IType _out107;
          _out107 = (this).GenType(_1470_instanceType, DCOMP.GenTypeContext.@default());
          _1475_tpe = _out107;
          if ((_1469_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1475_tpe = RAST.Type.create_Borrowed(_1475_tpe);
          } else if ((_1469_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1475_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1475_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1475_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _1475_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.__default.SelfOwned));
              } else {
                _1475_tpe = RAST.Type.create_Borrowed(RAST.__default.SelfOwned);
              }
            }
          }
          _1460_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1469_selfId, _1475_tpe)), _1460_params);
        }
        _1468_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1469_selfId, _1470_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1476_retTypeArgs;
      _1476_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1477_typeI;
      _1477_typeI = BigInteger.Zero;
      while ((_1477_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1478_typeExpr;
        RAST._IType _out108;
        _out108 = (this).GenType(((m).dtor_outTypes).Select(_1477_typeI), DCOMP.GenTypeContext.@default());
        _1478_typeExpr = _out108;
        _1476_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1476_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1478_typeExpr));
        _1477_typeI = (_1477_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1479_visibility;
      _1479_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1480_typeParamsFiltered;
      _1480_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1481_typeParamI = BigInteger.Zero; _1481_typeParamI < _hi28; _1481_typeParamI++) {
        DAST._ITypeArgDecl _1482_typeParam;
        _1482_typeParam = ((m).dtor_typeParams).Select(_1481_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1482_typeParam).dtor_name)))) {
          _1480_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1480_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1482_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1483_typeParams;
      _1483_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1480_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi29 = new BigInteger((_1480_typeParamsFiltered).Count);
        for (BigInteger _1484_i = BigInteger.Zero; _1484_i < _hi29; _1484_i++) {
          DAST._IType _1485_typeArg;
          RAST._ITypeParamDecl _1486_rTypeParamDecl;
          DAST._IType _out109;
          RAST._ITypeParamDecl _out110;
          (this).GenTypeParam((_1480_typeParamsFiltered).Select(_1484_i), out _out109, out _out110);
          _1485_typeArg = _out109;
          _1486_rTypeParamDecl = _out110;
          var _pat_let_tv142 = _1486_rTypeParamDecl;
          _1486_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1486_rTypeParamDecl, _pat_let34_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let34_0, _1487_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv142).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait)), _pat_let35_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let35_0, _1488_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1487_dt__update__tmp_h1).dtor_content, _1488_dt__update_hconstraints_h0)))));
          _1483_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1483_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1486_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1489_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1490_env = DCOMP.Environment.Default();
      RAST._IExpr _1491_preBody;
      _1491_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1492_preAssignNames;
      _1492_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1493_preAssignTypes;
      _1493_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1494_earlyReturn;
        _1494_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source72 = (m).dtor_outVars;
        bool unmatched72 = true;
        if (unmatched72) {
          if (_source72.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1495_outVars = _source72.dtor_value;
            unmatched72 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1494_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi30 = new BigInteger((_1495_outVars).Count);
                for (BigInteger _1496_outI = BigInteger.Zero; _1496_outI < _hi30; _1496_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1497_outVar;
                  _1497_outVar = (_1495_outVars).Select(_1496_outI);
                  Dafny.ISequence<Dafny.Rune> _1498_outName;
                  _1498_outName = DCOMP.__default.escapeVar(_1497_outVar);
                  Dafny.ISequence<Dafny.Rune> _1499_tracker__name;
                  _1499_tracker__name = DCOMP.__default.AddAssignedPrefix(_1498_outName);
                  _1492_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1492_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1499_tracker__name));
                  _1493_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1493_preAssignTypes, _1499_tracker__name, RAST.Type.create_Bool());
                  _1491_preBody = (_1491_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1499_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1500_tupleArgs;
                _1500_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi31 = new BigInteger((_1495_outVars).Count);
                for (BigInteger _1501_outI = BigInteger.Zero; _1501_outI < _hi31; _1501_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1502_outVar;
                  _1502_outVar = (_1495_outVars).Select(_1501_outI);
                  RAST._IType _1503_outType;
                  RAST._IType _out111;
                  _out111 = (this).GenType(((m).dtor_outTypes).Select(_1501_outI), DCOMP.GenTypeContext.@default());
                  _1503_outType = _out111;
                  Dafny.ISequence<Dafny.Rune> _1504_outName;
                  _1504_outName = DCOMP.__default.escapeVar(_1502_outVar);
                  _1461_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1461_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1504_outName));
                  RAST._IType _1505_outMaybeType;
                  _1505_outMaybeType = (((_1503_outType).CanReadWithoutClone()) ? (_1503_outType) : (RAST.__default.MaybePlaceboType(_1503_outType)));
                  _1462_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1462_paramTypes, _1504_outName, _1505_outMaybeType);
                  _1500_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1500_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1504_outName));
                }
                _1494_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_1500_tupleArgs);
              }
            }
          }
        }
        if (unmatched72) {
          unmatched72 = false;
        }
        _1490_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1492_preAssignNames, _1461_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1493_preAssignTypes, _1462_paramTypes));
        RAST._IExpr _1506_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1507___v69;
        DCOMP._IEnvironment _1508___v70;
        RAST._IExpr _out112;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out113;
        DCOMP._IEnvironment _out114;
        (this).GenStmts((m).dtor_body, _1468_selfIdent, _1490_env, true, _1494_earlyReturn, out _out112, out _out113, out _out114);
        _1506_body = _out112;
        _1507___v69 = _out113;
        _1508___v70 = _out114;
        _1489_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1491_preBody).Then(_1506_body));
      } else {
        _1490_env = DCOMP.Environment.create(_1461_paramNames, _1462_paramTypes);
        _1489_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1479_visibility, RAST.Fn.create(_1467_fnName, _1483_typeParams, _1460_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1476_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1476_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1476_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1489_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1509_declarations;
      _1509_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1510_i;
      _1510_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1511_stmts;
      _1511_stmts = stmts;
      while ((_1510_i) < (new BigInteger((_1511_stmts).Count))) {
        DAST._IStatement _1512_stmt;
        _1512_stmt = (_1511_stmts).Select(_1510_i);
        DAST._IStatement _source73 = _1512_stmt;
        bool unmatched73 = true;
        if (unmatched73) {
          if (_source73.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1513_name = _source73.dtor_name;
            DAST._IType _1514_optType = _source73.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source73.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched73 = false;
              if (((_1510_i) + (BigInteger.One)) < (new BigInteger((_1511_stmts).Count))) {
                DAST._IStatement _source74 = (_1511_stmts).Select((_1510_i) + (BigInteger.One));
                bool unmatched74 = true;
                if (unmatched74) {
                  if (_source74.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source74.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> _1515_name2 = lhs0.dtor_ident;
                      DAST._IExpression _1516_rhs = _source74.dtor_value;
                      unmatched74 = false;
                      if (object.Equals(_1515_name2, _1513_name)) {
                        _1511_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1511_stmts).Subsequence(BigInteger.Zero, _1510_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1513_name, _1514_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1516_rhs)))), (_1511_stmts).Drop((_1510_i) + (new BigInteger(2))));
                        _1512_stmt = (_1511_stmts).Select(_1510_i);
                      }
                    }
                  }
                }
                if (unmatched74) {
                  unmatched74 = false;
                }
              }
            }
          }
        }
        if (unmatched73) {
          unmatched73 = false;
        }
        RAST._IExpr _1517_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1518_recIdents;
        DCOMP._IEnvironment _1519_newEnv2;
        RAST._IExpr _out115;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
        DCOMP._IEnvironment _out117;
        (this).GenStmt(_1512_stmt, selfIdent, newEnv, (isLast) && ((_1510_i) == ((new BigInteger((_1511_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out115, out _out116, out _out117);
        _1517_stmtExpr = _out115;
        _1518_recIdents = _out116;
        _1519_newEnv2 = _out117;
        newEnv = _1519_newEnv2;
        DAST._IStatement _source75 = _1512_stmt;
        bool unmatched75 = true;
        if (unmatched75) {
          if (_source75.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1520_name = _source75.dtor_name;
            unmatched75 = false;
            {
              _1509_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1509_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_1520_name)));
            }
          }
        }
        if (unmatched75) {
          unmatched75 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1518_recIdents, _1509_declarations));
        generated = (generated).Then(_1517_stmtExpr);
        _1510_i = (_1510_i) + (BigInteger.One);
        if ((_1517_stmtExpr).is_Return) {
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
      DAST._IAssignLhs _source76 = lhs;
      bool unmatched76 = true;
      if (unmatched76) {
        if (_source76.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1521_id = _source76.dtor_ident;
          unmatched76 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1522_idRust;
            _1522_idRust = DCOMP.__default.escapeVar(_1521_id);
            if (((env).IsBorrowed(_1522_idRust)) || ((env).IsBorrowedMut(_1522_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1522_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1522_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1522_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Select) {
          DAST._IExpression _1523_on = _source76.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1524_field = _source76.dtor_field;
          unmatched76 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1525_fieldName;
            _1525_fieldName = DCOMP.__default.escapeVar(_1524_field);
            RAST._IExpr _1526_onExpr;
            DCOMP._IOwnership _1527_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1528_recIdents;
            RAST._IExpr _out118;
            DCOMP._IOwnership _out119;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
            (this).GenExpr(_1523_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out118, out _out119, out _out120);
            _1526_onExpr = _out118;
            _1527_onOwned = _out119;
            _1528_recIdents = _out120;
            RAST._IExpr _source77 = _1526_onExpr;
            bool unmatched77 = true;
            if (unmatched77) {
              bool disjunctiveMatch11 = false;
              if (_source77.is_Call) {
                RAST._IExpr obj2 = _source77.dtor_obj;
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
              if (_source77.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name6 = _source77.dtor_name;
                if (object.Equals(name6, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch11 = true;
                }
              }
              if (_source77.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op14 = _source77.dtor_op1;
                if (object.Equals(op14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying4 = _source77.dtor_underlying;
                  if (underlying4.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name7 = underlying4.dtor_name;
                    if (object.Equals(name7, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      disjunctiveMatch11 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch11) {
                unmatched77 = false;
                Dafny.ISequence<Dafny.Rune> _1529_isAssignedVar;
                _1529_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1525_fieldName);
                if (((newEnv).dtor_names).Contains(_1529_isAssignedVar)) {
                  generated = (((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1525_fieldName), RAST.Expr.create_Identifier(_1529_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1529_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1529_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1525_fieldName, rhs);
                }
              }
            }
            if (unmatched77) {
              unmatched77 = false;
              if (!object.Equals(_1526_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1526_onExpr = ((this).modify__macro).Apply1(_1526_onExpr);
              }
              generated = RAST.__default.AssignMember(_1526_onExpr, _1525_fieldName, rhs);
            }
            readIdents = _1528_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched76) {
        DAST._IExpression _1530_on = _source76.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1531_indices = _source76.dtor_indices;
        unmatched76 = false;
        {
          RAST._IExpr _1532_onExpr;
          DCOMP._IOwnership _1533_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1534_recIdents;
          RAST._IExpr _out121;
          DCOMP._IOwnership _out122;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
          (this).GenExpr(_1530_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out121, out _out122, out _out123);
          _1532_onExpr = _out121;
          _1533_onOwned = _out122;
          _1534_recIdents = _out123;
          readIdents = _1534_recIdents;
          _1532_onExpr = ((this).modify__macro).Apply1(_1532_onExpr);
          RAST._IExpr _1535_r;
          _1535_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1536_indicesExpr;
          _1536_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_1531_indices).Count);
          for (BigInteger _1537_i = BigInteger.Zero; _1537_i < _hi32; _1537_i++) {
            RAST._IExpr _1538_idx;
            DCOMP._IOwnership _1539___v79;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1540_recIdentsIdx;
            RAST._IExpr _out124;
            DCOMP._IOwnership _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            (this).GenExpr((_1531_indices).Select(_1537_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out124, out _out125, out _out126);
            _1538_idx = _out124;
            _1539___v79 = _out125;
            _1540_recIdentsIdx = _out126;
            Dafny.ISequence<Dafny.Rune> _1541_varName;
            _1541_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1537_i));
            _1536_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1536_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1541_varName)));
            _1535_r = (_1535_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1541_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1538_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1540_recIdentsIdx);
          }
          if ((new BigInteger((_1531_indices).Count)) > (BigInteger.One)) {
            _1532_onExpr = (_1532_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1542_rhs;
          _1542_rhs = rhs;
          var _pat_let_tv143 = env;
          if (((_1532_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1532_onExpr).LhsIdentifierName(), _pat_let36_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let36_0, _1543_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv143).GetType(_1543_name), _pat_let37_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let37_0, _1544_tpe => ((_1544_tpe).is_Some) && (((_1544_tpe).dtor_value).IsUninitArray())))))))) {
            _1542_rhs = RAST.__default.MaybeUninitNew(_1542_rhs);
          }
          generated = (_1535_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1532_onExpr, _1536_indicesExpr)), _1542_rhs));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source78 = stmt;
      bool unmatched78 = true;
      if (unmatched78) {
        if (_source78.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1545_fields = _source78.dtor_fields;
          unmatched78 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi33 = new BigInteger((_1545_fields).Count);
            for (BigInteger _1546_i = BigInteger.Zero; _1546_i < _hi33; _1546_i++) {
              DAST._IFormal _1547_field;
              _1547_field = (_1545_fields).Select(_1546_i);
              Dafny.ISequence<Dafny.Rune> _1548_fieldName;
              _1548_fieldName = DCOMP.__default.escapeVar((_1547_field).dtor_name);
              RAST._IType _1549_fieldTyp;
              RAST._IType _out127;
              _out127 = (this).GenType((_1547_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1549_fieldTyp = _out127;
              Dafny.ISequence<Dafny.Rune> _1550_isAssignedVar;
              _1550_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1548_fieldName);
              if (((newEnv).dtor_names).Contains(_1550_isAssignedVar)) {
                RAST._IExpr _1551_rhs;
                DCOMP._IOwnership _1552___v80;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1553___v81;
                RAST._IExpr _out128;
                DCOMP._IOwnership _out129;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1547_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out128, out _out129, out _out130);
                _1551_rhs = _out128;
                _1552___v80 = _out129;
                _1553___v81 = _out130;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1550_isAssignedVar));
                generated = (generated).Then((((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1548_fieldName), RAST.Expr.create_Identifier(_1550_isAssignedVar), _1551_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1550_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1554_name = _source78.dtor_name;
          DAST._IType _1555_typ = _source78.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source78.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1556_expression = maybeValue1.dtor_value;
            unmatched78 = false;
            {
              RAST._IType _1557_tpe;
              RAST._IType _out131;
              _out131 = (this).GenType(_1555_typ, DCOMP.GenTypeContext.InBinding());
              _1557_tpe = _out131;
              Dafny.ISequence<Dafny.Rune> _1558_varName;
              _1558_varName = DCOMP.__default.escapeVar(_1554_name);
              bool _1559_hasCopySemantics;
              _1559_hasCopySemantics = (_1557_tpe).CanReadWithoutClone();
              if (((_1556_expression).is_InitializationValue) && (!(_1559_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1558_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.MaybePlaceboPath).AsExpr()).ApplyType1(_1557_tpe)).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1558_varName, RAST.__default.MaybePlaceboType(_1557_tpe));
              } else {
                RAST._IExpr _1560_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1561_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1556_expression).is_InitializationValue) && ((_1557_tpe).IsObjectOrPointer())) {
                  _1560_expr = (_1557_tpe).ToNullExpr();
                  _1561_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1562_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out132;
                  DCOMP._IOwnership _out133;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out134;
                  (this).GenExpr(_1556_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out132, out _out133, out _out134);
                  _1560_expr = _out132;
                  _1562_exprOwnership = _out133;
                  _1561_recIdents = _out134;
                }
                readIdents = _1561_recIdents;
                _1557_tpe = (((_1556_expression).is_NewUninitArray) ? ((_1557_tpe).TypeAtInitialization()) : (_1557_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1558_varName, Std.Wrappers.Option<RAST._IType>.create_Some(_1557_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1560_expr));
                newEnv = (env).AddAssigned(_1558_varName, _1557_tpe);
              }
            }
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1563_name = _source78.dtor_name;
          DAST._IType _1564_typ = _source78.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source78.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched78 = false;
            {
              DAST._IStatement _1565_newStmt;
              _1565_newStmt = DAST.Statement.create_DeclareVar(_1563_name, _1564_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1564_typ)));
              RAST._IExpr _out135;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out136;
              DCOMP._IEnvironment _out137;
              (this).GenStmt(_1565_newStmt, selfIdent, env, isLast, earlyReturn, out _out135, out _out136, out _out137);
              generated = _out135;
              readIdents = _out136;
              newEnv = _out137;
            }
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_Assign) {
          DAST._IAssignLhs _1566_lhs = _source78.dtor_lhs;
          DAST._IExpression _1567_expression = _source78.dtor_value;
          unmatched78 = false;
          {
            RAST._IExpr _1568_exprGen;
            DCOMP._IOwnership _1569___v82;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1570_exprIdents;
            RAST._IExpr _out138;
            DCOMP._IOwnership _out139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
            (this).GenExpr(_1567_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out138, out _out139, out _out140);
            _1568_exprGen = _out138;
            _1569___v82 = _out139;
            _1570_exprIdents = _out140;
            if ((_1566_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1571_rustId;
              _1571_rustId = DCOMP.__default.escapeVar((_1566_lhs).dtor_ident);
              Std.Wrappers._IOption<RAST._IType> _1572_tpe;
              _1572_tpe = (env).GetType(_1571_rustId);
              if (((_1572_tpe).is_Some) && ((((_1572_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1568_exprGen = RAST.__default.MaybePlacebo(_1568_exprGen);
              }
            }
            if (((_1566_lhs).is_Index) && (((_1566_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1573_rustId;
              _1573_rustId = DCOMP.__default.escapeVar(((_1566_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1574_tpe;
              _1574_tpe = (env).GetType(_1573_rustId);
              if (((_1574_tpe).is_Some) && ((((_1574_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1568_exprGen = RAST.__default.MaybeUninitNew(_1568_exprGen);
              }
            }
            RAST._IExpr _1575_lhsGen;
            bool _1576_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1577_recIdents;
            DCOMP._IEnvironment _1578_resEnv;
            RAST._IExpr _out141;
            bool _out142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
            DCOMP._IEnvironment _out144;
            (this).GenAssignLhs(_1566_lhs, _1568_exprGen, selfIdent, env, out _out141, out _out142, out _out143, out _out144);
            _1575_lhsGen = _out141;
            _1576_needsIIFE = _out142;
            _1577_recIdents = _out143;
            _1578_resEnv = _out144;
            generated = _1575_lhsGen;
            newEnv = _1578_resEnv;
            if (_1576_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1577_recIdents, _1570_exprIdents);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_If) {
          DAST._IExpression _1579_cond = _source78.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1580_thnDafny = _source78.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1581_elsDafny = _source78.dtor_els;
          unmatched78 = false;
          {
            RAST._IExpr _1582_cond;
            DCOMP._IOwnership _1583___v83;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1584_recIdents;
            RAST._IExpr _out145;
            DCOMP._IOwnership _out146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
            (this).GenExpr(_1579_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out145, out _out146, out _out147);
            _1582_cond = _out145;
            _1583___v83 = _out146;
            _1584_recIdents = _out147;
            Dafny.ISequence<Dafny.Rune> _1585_condString;
            _1585_condString = (_1582_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1584_recIdents;
            RAST._IExpr _1586_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1587_thnIdents;
            DCOMP._IEnvironment _1588_thnEnv;
            RAST._IExpr _out148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
            DCOMP._IEnvironment _out150;
            (this).GenStmts(_1580_thnDafny, selfIdent, env, isLast, earlyReturn, out _out148, out _out149, out _out150);
            _1586_thn = _out148;
            _1587_thnIdents = _out149;
            _1588_thnEnv = _out150;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1587_thnIdents);
            RAST._IExpr _1589_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1590_elsIdents;
            DCOMP._IEnvironment _1591_elsEnv;
            RAST._IExpr _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP._IEnvironment _out153;
            (this).GenStmts(_1581_elsDafny, selfIdent, env, isLast, earlyReturn, out _out151, out _out152, out _out153);
            _1589_els = _out151;
            _1590_elsIdents = _out152;
            _1591_elsEnv = _out153;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1590_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1582_cond, _1586_thn, _1589_els);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1592_lbl = _source78.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1593_body = _source78.dtor_body;
          unmatched78 = false;
          {
            RAST._IExpr _1594_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1595_bodyIdents;
            DCOMP._IEnvironment _1596_env2;
            RAST._IExpr _out154;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out155;
            DCOMP._IEnvironment _out156;
            (this).GenStmts(_1593_body, selfIdent, env, isLast, earlyReturn, out _out154, out _out155, out _out156);
            _1594_body = _out154;
            _1595_bodyIdents = _out155;
            _1596_env2 = _out156;
            readIdents = _1595_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1592_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1594_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_While) {
          DAST._IExpression _1597_cond = _source78.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1598_body = _source78.dtor_body;
          unmatched78 = false;
          {
            RAST._IExpr _1599_cond;
            DCOMP._IOwnership _1600___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1601_recIdents;
            RAST._IExpr _out157;
            DCOMP._IOwnership _out158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
            (this).GenExpr(_1597_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out157, out _out158, out _out159);
            _1599_cond = _out157;
            _1600___v84 = _out158;
            _1601_recIdents = _out159;
            readIdents = _1601_recIdents;
            RAST._IExpr _1602_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1603_bodyIdents;
            DCOMP._IEnvironment _1604_bodyEnv;
            RAST._IExpr _out160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out161;
            DCOMP._IEnvironment _out162;
            (this).GenStmts(_1598_body, selfIdent, env, false, earlyReturn, out _out160, out _out161, out _out162);
            _1602_bodyExpr = _out160;
            _1603_bodyIdents = _out161;
            _1604_bodyEnv = _out162;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1603_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1599_cond), _1602_bodyExpr);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1605_boundName = _source78.dtor_boundName;
          DAST._IType _1606_boundType = _source78.dtor_boundType;
          DAST._IExpression _1607_overExpr = _source78.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1608_body = _source78.dtor_body;
          unmatched78 = false;
          {
            RAST._IExpr _1609_over;
            DCOMP._IOwnership _1610___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1611_recIdents;
            RAST._IExpr _out163;
            DCOMP._IOwnership _out164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
            (this).GenExpr(_1607_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out163, out _out164, out _out165);
            _1609_over = _out163;
            _1610___v85 = _out164;
            _1611_recIdents = _out165;
            if (((_1607_overExpr).is_MapBoundedPool) || ((_1607_overExpr).is_SetBoundedPool)) {
              _1609_over = ((_1609_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1612_boundTpe;
            RAST._IType _out166;
            _out166 = (this).GenType(_1606_boundType, DCOMP.GenTypeContext.@default());
            _1612_boundTpe = _out166;
            readIdents = _1611_recIdents;
            Dafny.ISequence<Dafny.Rune> _1613_boundRName;
            _1613_boundRName = DCOMP.__default.escapeVar(_1605_boundName);
            RAST._IExpr _1614_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1615_bodyIdents;
            DCOMP._IEnvironment _1616_bodyEnv;
            RAST._IExpr _out167;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out168;
            DCOMP._IEnvironment _out169;
            (this).GenStmts(_1608_body, selfIdent, (env).AddAssigned(_1613_boundRName, _1612_boundTpe), false, earlyReturn, out _out167, out _out168, out _out169);
            _1614_bodyExpr = _out167;
            _1615_bodyIdents = _out168;
            _1616_bodyEnv = _out169;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1615_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1613_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1613_boundRName, _1609_over, _1614_bodyExpr);
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1617_toLabel = _source78.dtor_toLabel;
          unmatched78 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source79 = _1617_toLabel;
            bool unmatched79 = true;
            if (unmatched79) {
              if (_source79.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1618_lbl = _source79.dtor_value;
                unmatched79 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1618_lbl)));
                }
              }
            }
            if (unmatched79) {
              unmatched79 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1619_body = _source78.dtor_body;
          unmatched78 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1620_selfClone;
              DCOMP._IOwnership _1621___v86;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1622___v87;
              RAST._IExpr _out170;
              DCOMP._IOwnership _out171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out172;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out170, out _out171, out _out172);
              _1620_selfClone = _out170;
              _1621___v86 = _out171;
              _1622___v87 = _out172;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1620_selfClone)));
            }
            newEnv = env;
            BigInteger _hi34 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1623_paramI = BigInteger.Zero; _1623_paramI < _hi34; _1623_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1624_param;
              _1624_param = ((env).dtor_names).Select(_1623_paramI);
              RAST._IExpr _1625_paramInit;
              DCOMP._IOwnership _1626___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1627___v89;
              RAST._IExpr _out173;
              DCOMP._IOwnership _out174;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out175;
              (this).GenIdent(_1624_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out173, out _out174, out _out175);
              _1625_paramInit = _out173;
              _1626___v88 = _out174;
              _1627___v89 = _out175;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1624_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1625_paramInit)));
              if (((env).dtor_types).Contains(_1624_param)) {
                RAST._IType _1628_declaredType;
                _1628_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1624_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1624_param, _1628_declaredType);
              }
            }
            RAST._IExpr _1629_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1630_bodyIdents;
            DCOMP._IEnvironment _1631_bodyEnv;
            RAST._IExpr _out176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
            DCOMP._IEnvironment _out178;
            (this).GenStmts(_1619_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out176, out _out177, out _out178);
            _1629_bodyExpr = _out176;
            _1630_bodyIdents = _out177;
            _1631_bodyEnv = _out178;
            readIdents = _1630_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1629_bodyExpr)));
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_JumpTailCallStart) {
          unmatched78 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_Call) {
          DAST._IExpression _1632_on = _source78.dtor_on;
          DAST._ICallName _1633_name = _source78.dtor_callName;
          Dafny.ISequence<DAST._IType> _1634_typeArgs = _source78.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1635_args = _source78.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1636_maybeOutVars = _source78.dtor_outs;
          unmatched78 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1637_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1638_recIdents;
            Dafny.ISequence<RAST._IType> _1639_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1640_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out180;
            Dafny.ISequence<RAST._IType> _out181;
            Std.Wrappers._IOption<DAST._IResolvedType> _out182;
            (this).GenArgs(selfIdent, _1633_name, _1634_typeArgs, _1635_args, env, out _out179, out _out180, out _out181, out _out182);
            _1637_argExprs = _out179;
            _1638_recIdents = _out180;
            _1639_typeExprs = _out181;
            _1640_fullNameQualifier = _out182;
            readIdents = _1638_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source80 = _1640_fullNameQualifier;
            bool unmatched80 = true;
            if (unmatched80) {
              if (_source80.is_Some) {
                DAST._IResolvedType value9 = _source80.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1641_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1642_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1643_base = value9.dtor_kind;
                unmatched80 = false;
                RAST._IExpr _1644_fullPath;
                RAST._IExpr _out183;
                _out183 = DCOMP.COMP.GenPathExpr(_1641_path, true);
                _1644_fullPath = _out183;
                Dafny.ISequence<RAST._IType> _1645_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out184;
                _out184 = (this).GenTypeArgs(_1642_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1645_onTypeExprs = _out184;
                RAST._IExpr _1646_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1647_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1648_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1643_base).is_Trait) || ((_1643_base).is_Class)) {
                  RAST._IExpr _out185;
                  DCOMP._IOwnership _out186;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out187;
                  (this).GenExpr(_1632_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out185, out _out186, out _out187);
                  _1646_onExpr = _out185;
                  _1647_recOwnership = _out186;
                  _1648_recIdents = _out187;
                  _1646_onExpr = ((this).modify__macro).Apply1(_1646_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1648_recIdents);
                } else {
                  RAST._IExpr _out188;
                  DCOMP._IOwnership _out189;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
                  (this).GenExpr(_1632_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out188, out _out189, out _out190);
                  _1646_onExpr = _out188;
                  _1647_recOwnership = _out189;
                  _1648_recIdents = _out190;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1648_recIdents);
                }
                generated = ((((_1644_fullPath).ApplyType(_1645_onTypeExprs)).FSel(DCOMP.__default.escapeName((_1633_name).dtor_name))).ApplyType(_1639_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1646_onExpr), _1637_argExprs));
              }
            }
            if (unmatched80) {
              unmatched80 = false;
              RAST._IExpr _1649_onExpr;
              DCOMP._IOwnership _1650___v94;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1651_enclosingIdents;
              RAST._IExpr _out191;
              DCOMP._IOwnership _out192;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
              (this).GenExpr(_1632_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out191, out _out192, out _out193);
              _1649_onExpr = _out191;
              _1650___v94 = _out192;
              _1651_enclosingIdents = _out193;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1651_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1652_renderedName;
              _1652_renderedName = (this).GetMethodName(_1632_on, _1633_name);
              DAST._IExpression _source81 = _1632_on;
              bool unmatched81 = true;
              if (unmatched81) {
                bool disjunctiveMatch12 = false;
                if (_source81.is_Companion) {
                  disjunctiveMatch12 = true;
                }
                if (_source81.is_ExternCompanion) {
                  disjunctiveMatch12 = true;
                }
                if (disjunctiveMatch12) {
                  unmatched81 = false;
                  {
                    _1649_onExpr = (_1649_onExpr).FSel(_1652_renderedName);
                  }
                }
              }
              if (unmatched81) {
                unmatched81 = false;
                {
                  if (!object.Equals(_1649_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source82 = _1633_name;
                    bool unmatched82 = true;
                    if (unmatched82) {
                      if (_source82.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source82.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1653_tpe = onType0.dtor_value;
                          unmatched82 = false;
                          RAST._IType _1654_typ;
                          RAST._IType _out194;
                          _out194 = (this).GenType(_1653_tpe, DCOMP.GenTypeContext.@default());
                          _1654_typ = _out194;
                          if (((_1654_typ).IsObjectOrPointer()) && (!object.Equals(_1649_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1649_onExpr = ((this).modify__macro).Apply1(_1649_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched82) {
                      unmatched82 = false;
                    }
                  }
                  _1649_onExpr = (_1649_onExpr).Sel(_1652_renderedName);
                }
              }
              generated = ((_1649_onExpr).ApplyType(_1639_typeExprs)).Apply(_1637_argExprs);
            }
            if (((_1636_maybeOutVars).is_Some) && ((new BigInteger(((_1636_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1655_outVar;
              _1655_outVar = DCOMP.__default.escapeVar(((_1636_maybeOutVars).dtor_value).Select(BigInteger.Zero));
              if (!((env).CanReadWithoutClone(_1655_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1655_outVar, generated);
            } else if (((_1636_maybeOutVars).is_None) || ((new BigInteger(((_1636_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1656_tmpVar;
              _1656_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1657_tmpId;
              _1657_tmpId = RAST.Expr.create_Identifier(_1656_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1656_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1658_outVars;
              _1658_outVars = (_1636_maybeOutVars).dtor_value;
              BigInteger _hi35 = new BigInteger((_1658_outVars).Count);
              for (BigInteger _1659_outI = BigInteger.Zero; _1659_outI < _hi35; _1659_outI++) {
                Dafny.ISequence<Dafny.Rune> _1660_outVar;
                _1660_outVar = DCOMP.__default.escapeVar((_1658_outVars).Select(_1659_outI));
                RAST._IExpr _1661_rhs;
                _1661_rhs = (_1657_tmpId).Sel(Std.Strings.__default.OfNat(_1659_outI));
                if (!((env).CanReadWithoutClone(_1660_outVar))) {
                  _1661_rhs = RAST.__default.MaybePlacebo(_1661_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1660_outVar, _1661_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_Return) {
          DAST._IExpression _1662_exprDafny = _source78.dtor_expr;
          unmatched78 = false;
          {
            RAST._IExpr _1663_expr;
            DCOMP._IOwnership _1664___v104;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1665_recIdents;
            RAST._IExpr _out195;
            DCOMP._IOwnership _out196;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
            (this).GenExpr(_1662_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out195, out _out196, out _out197);
            _1663_expr = _out195;
            _1664___v104 = _out196;
            _1665_recIdents = _out197;
            readIdents = _1665_recIdents;
            if (isLast) {
              generated = _1663_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1663_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_EarlyReturn) {
          unmatched78 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source83 = earlyReturn;
            bool unmatched83 = true;
            if (unmatched83) {
              if (_source83.is_None) {
                unmatched83 = false;
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
              }
            }
            if (unmatched83) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1666_rustIdents = _source83.dtor_value;
              unmatched83 = false;
              Dafny.ISequence<RAST._IExpr> _1667_tupleArgs;
              _1667_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi36 = new BigInteger((_1666_rustIdents).Count);
              for (BigInteger _1668_i = BigInteger.Zero; _1668_i < _hi36; _1668_i++) {
                RAST._IExpr _1669_rIdent;
                DCOMP._IOwnership _1670___v105;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1671___v106;
                RAST._IExpr _out198;
                DCOMP._IOwnership _out199;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out200;
                (this).GenIdent((_1666_rustIdents).Select(_1668_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out198, out _out199, out _out200);
                _1669_rIdent = _out198;
                _1670___v105 = _out199;
                _1671___v106 = _out200;
                _1667_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1667_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1669_rIdent));
              }
              if ((new BigInteger((_1667_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1667_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1667_tupleArgs)));
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched78) {
        if (_source78.is_Halt) {
          unmatched78 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched78) {
        DAST._IExpression _1672_e = _source78.dtor_Print_a0;
        unmatched78 = false;
        {
          RAST._IExpr _1673_printedExpr;
          DCOMP._IOwnership _1674_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1675_recIdents;
          RAST._IExpr _out201;
          DCOMP._IOwnership _out202;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out203;
          (this).GenExpr(_1672_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out201, out _out202, out _out203);
          _1673_printedExpr = _out201;
          _1674_recOwnership = _out202;
          _1675_recIdents = _out203;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).AsExpr()).Apply1(_1673_printedExpr)));
          readIdents = _1675_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeRangeToRustType(DAST._INewtypeRange range) {
      DAST._INewtypeRange _source84 = range;
      bool unmatched84 = true;
      if (unmatched84) {
        if (_source84.is_NoRange) {
          unmatched84 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched84) {
        if (_source84.is_U8) {
          unmatched84 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched84) {
        if (_source84.is_U16) {
          unmatched84 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched84) {
        if (_source84.is_U32) {
          unmatched84 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched84) {
        if (_source84.is_U64) {
          unmatched84 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched84) {
        if (_source84.is_U128) {
          unmatched84 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched84) {
        if (_source84.is_I8) {
          unmatched84 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched84) {
        if (_source84.is_I16) {
          unmatched84 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched84) {
        if (_source84.is_I32) {
          unmatched84 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched84) {
        if (_source84.is_I64) {
          unmatched84 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched84) {
        if (_source84.is_I128) {
          unmatched84 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched84) {
        unmatched84 = false;
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
      DAST._IExpression _source85 = e;
      bool unmatched85 = true;
      if (unmatched85) {
        if (_source85.is_Literal) {
          DAST._ILiteral _h170 = _source85.dtor_Literal_a0;
          if (_h170.is_BoolLiteral) {
            bool _1676_b = _h170.dtor_BoolLiteral_a0;
            unmatched85 = false;
            {
              RAST._IExpr _out208;
              DCOMP._IOwnership _out209;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1676_b), expectedOwnership, out _out208, out _out209);
              r = _out208;
              resultingOwnership = _out209;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched85) {
        if (_source85.is_Literal) {
          DAST._ILiteral _h171 = _source85.dtor_Literal_a0;
          if (_h171.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1677_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1678_t = _h171.dtor_IntLiteral_a1;
            unmatched85 = false;
            {
              DAST._IType _source86 = _1678_t;
              bool unmatched86 = true;
              if (unmatched86) {
                if (_source86.is_Primitive) {
                  DAST._IPrimitive _h70 = _source86.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched86 = false;
                    {
                      if ((new BigInteger((_1677_i).Count)) <= (new BigInteger(4))) {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralInt(_1677_i));
                      } else {
                        r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1677_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched86) {
                DAST._IType _1679_o = _source86;
                unmatched86 = false;
                {
                  RAST._IType _1680_genType;
                  RAST._IType _out210;
                  _out210 = (this).GenType(_1679_o, DCOMP.GenTypeContext.@default());
                  _1680_genType = _out210;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1677_i), _1680_genType);
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
      if (unmatched85) {
        if (_source85.is_Literal) {
          DAST._ILiteral _h172 = _source85.dtor_Literal_a0;
          if (_h172.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1681_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1682_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1683_t = _h172.dtor_DecLiteral_a2;
            unmatched85 = false;
            {
              DAST._IType _source87 = _1683_t;
              bool unmatched87 = true;
              if (unmatched87) {
                if (_source87.is_Primitive) {
                  DAST._IPrimitive _h71 = _source87.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched87 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1681_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1682_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched87) {
                DAST._IType _1684_o = _source87;
                unmatched87 = false;
                {
                  RAST._IType _1685_genType;
                  RAST._IType _out213;
                  _out213 = (this).GenType(_1684_o, DCOMP.GenTypeContext.@default());
                  _1685_genType = _out213;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1681_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1682_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1685_genType);
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
      if (unmatched85) {
        if (_source85.is_Literal) {
          DAST._ILiteral _h173 = _source85.dtor_Literal_a0;
          if (_h173.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1686_l = _h173.dtor_StringLiteral_a0;
            bool _1687_verbatim = _h173.dtor_verbatim;
            unmatched85 = false;
            {
              if (_1687_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = (((RAST.__default.dafny__runtime).MSel((this).string__of)).AsExpr()).Apply1(RAST.Expr.create_LiteralString(_1686_l, false, _1687_verbatim));
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
      if (unmatched85) {
        if (_source85.is_Literal) {
          DAST._ILiteral _h174 = _source85.dtor_Literal_a0;
          if (_h174.is_CharLiteralUTF16) {
            BigInteger _1688_c = _h174.dtor_CharLiteralUTF16_a0;
            unmatched85 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1688_c));
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
      if (unmatched85) {
        if (_source85.is_Literal) {
          DAST._ILiteral _h175 = _source85.dtor_Literal_a0;
          if (_h175.is_CharLiteral) {
            Dafny.Rune _1689_c = _h175.dtor_CharLiteral_a0;
            unmatched85 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1689_c).Value)));
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
      if (unmatched85) {
        DAST._ILiteral _h176 = _source85.dtor_Literal_a0;
        DAST._IType _1690_tpe = _h176.dtor_Null_a0;
        unmatched85 = false;
        {
          RAST._IType _1691_tpeGen;
          RAST._IType _out222;
          _out222 = (this).GenType(_1690_tpe, DCOMP.GenTypeContext.@default());
          _1691_tpeGen = _out222;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null_mut"));
          } else {
            r = RAST.Expr.create_TypeAscription((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1691_tpeGen);
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
      DAST._IBinOp _1692_op = _let_tmp_rhs54.dtor_op;
      DAST._IExpression _1693_lExpr = _let_tmp_rhs54.dtor_left;
      DAST._IExpression _1694_rExpr = _let_tmp_rhs54.dtor_right;
      DAST.Format._IBinaryOpFormat _1695_format = _let_tmp_rhs54.dtor_format2;
      bool _1696_becomesLeftCallsRight;
      _1696_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source88 = _1692_op;
        bool unmatched88 = true;
        if (unmatched88) {
          bool disjunctiveMatch13 = false;
          if (_source88.is_SetMerge) {
            disjunctiveMatch13 = true;
          }
          if (_source88.is_SetSubtraction) {
            disjunctiveMatch13 = true;
          }
          if (_source88.is_SetIntersection) {
            disjunctiveMatch13 = true;
          }
          if (_source88.is_SetDisjoint) {
            disjunctiveMatch13 = true;
          }
          if (_source88.is_MapMerge) {
            disjunctiveMatch13 = true;
          }
          if (_source88.is_MapSubtraction) {
            disjunctiveMatch13 = true;
          }
          if (_source88.is_MultisetMerge) {
            disjunctiveMatch13 = true;
          }
          if (_source88.is_MultisetSubtraction) {
            disjunctiveMatch13 = true;
          }
          if (_source88.is_MultisetIntersection) {
            disjunctiveMatch13 = true;
          }
          if (_source88.is_MultisetDisjoint) {
            disjunctiveMatch13 = true;
          }
          if (_source88.is_Concat) {
            disjunctiveMatch13 = true;
          }
          if (disjunctiveMatch13) {
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
      bool _1697_becomesRightCallsLeft;
      _1697_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source89 = _1692_op;
        bool unmatched89 = true;
        if (unmatched89) {
          if (_source89.is_In) {
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
      bool _1698_becomesCallLeftRight;
      _1698_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source90 = _1692_op;
        bool unmatched90 = true;
        if (unmatched90) {
          if (_source90.is_Eq) {
            bool referential0 = _source90.dtor_referential;
            if ((referential0) == (true)) {
              unmatched90 = false;
              return false;
            }
          }
        }
        if (unmatched90) {
          if (_source90.is_SetMerge) {
            unmatched90 = false;
            return true;
          }
        }
        if (unmatched90) {
          if (_source90.is_SetSubtraction) {
            unmatched90 = false;
            return true;
          }
        }
        if (unmatched90) {
          if (_source90.is_SetIntersection) {
            unmatched90 = false;
            return true;
          }
        }
        if (unmatched90) {
          if (_source90.is_SetDisjoint) {
            unmatched90 = false;
            return true;
          }
        }
        if (unmatched90) {
          if (_source90.is_MapMerge) {
            unmatched90 = false;
            return true;
          }
        }
        if (unmatched90) {
          if (_source90.is_MapSubtraction) {
            unmatched90 = false;
            return true;
          }
        }
        if (unmatched90) {
          if (_source90.is_MultisetMerge) {
            unmatched90 = false;
            return true;
          }
        }
        if (unmatched90) {
          if (_source90.is_MultisetSubtraction) {
            unmatched90 = false;
            return true;
          }
        }
        if (unmatched90) {
          if (_source90.is_MultisetIntersection) {
            unmatched90 = false;
            return true;
          }
        }
        if (unmatched90) {
          if (_source90.is_MultisetDisjoint) {
            unmatched90 = false;
            return true;
          }
        }
        if (unmatched90) {
          if (_source90.is_Concat) {
            unmatched90 = false;
            return true;
          }
        }
        if (unmatched90) {
          unmatched90 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1699_expectedLeftOwnership;
      _1699_expectedLeftOwnership = ((_1696_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1697_becomesRightCallsLeft) || (_1698_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1700_expectedRightOwnership;
      _1700_expectedRightOwnership = (((_1696_becomesLeftCallsRight) || (_1698_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1697_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1701_left;
      DCOMP._IOwnership _1702___v111;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1703_recIdentsL;
      RAST._IExpr _out225;
      DCOMP._IOwnership _out226;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
      (this).GenExpr(_1693_lExpr, selfIdent, env, _1699_expectedLeftOwnership, out _out225, out _out226, out _out227);
      _1701_left = _out225;
      _1702___v111 = _out226;
      _1703_recIdentsL = _out227;
      RAST._IExpr _1704_right;
      DCOMP._IOwnership _1705___v112;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1706_recIdentsR;
      RAST._IExpr _out228;
      DCOMP._IOwnership _out229;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out230;
      (this).GenExpr(_1694_rExpr, selfIdent, env, _1700_expectedRightOwnership, out _out228, out _out229, out _out230);
      _1704_right = _out228;
      _1705___v112 = _out229;
      _1706_recIdentsR = _out230;
      DAST._IBinOp _source91 = _1692_op;
      bool unmatched91 = true;
      if (unmatched91) {
        if (_source91.is_In) {
          unmatched91 = false;
          {
            r = ((_1704_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1701_left);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_SeqProperPrefix) {
          unmatched91 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1701_left, _1704_right, _1695_format);
        }
      }
      if (unmatched91) {
        if (_source91.is_SeqPrefix) {
          unmatched91 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1701_left, _1704_right, _1695_format);
        }
      }
      if (unmatched91) {
        if (_source91.is_SetMerge) {
          unmatched91 = false;
          {
            r = ((_1701_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1704_right);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_SetSubtraction) {
          unmatched91 = false;
          {
            r = ((_1701_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1704_right);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_SetIntersection) {
          unmatched91 = false;
          {
            r = ((_1701_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1704_right);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_Subset) {
          unmatched91 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1701_left, _1704_right, _1695_format);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_ProperSubset) {
          unmatched91 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1701_left, _1704_right, _1695_format);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_SetDisjoint) {
          unmatched91 = false;
          {
            r = ((_1701_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1704_right);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_MapMerge) {
          unmatched91 = false;
          {
            r = ((_1701_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1704_right);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_MapSubtraction) {
          unmatched91 = false;
          {
            r = ((_1701_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1704_right);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_MultisetMerge) {
          unmatched91 = false;
          {
            r = ((_1701_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1704_right);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_MultisetSubtraction) {
          unmatched91 = false;
          {
            r = ((_1701_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1704_right);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_MultisetIntersection) {
          unmatched91 = false;
          {
            r = ((_1701_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1704_right);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_Submultiset) {
          unmatched91 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1701_left, _1704_right, _1695_format);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_ProperSubmultiset) {
          unmatched91 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1701_left, _1704_right, _1695_format);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_MultisetDisjoint) {
          unmatched91 = false;
          {
            r = ((_1701_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1704_right);
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_Concat) {
          unmatched91 = false;
          {
            r = ((_1701_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1704_right);
          }
        }
      }
      if (unmatched91) {
        unmatched91 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1692_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1692_op), _1701_left, _1704_right, _1695_format);
          } else {
            DAST._IBinOp _source92 = _1692_op;
            bool unmatched92 = true;
            if (unmatched92) {
              if (_source92.is_Eq) {
                bool _1707_referential = _source92.dtor_referential;
                unmatched92 = false;
                {
                  if (_1707_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1701_left, _1704_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1694_rExpr).is_SeqValue) && ((new BigInteger(((_1694_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1701_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1693_lExpr).is_SeqValue) && ((new BigInteger(((_1693_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1704_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1701_left, _1704_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched92) {
              if (_source92.is_EuclidianDiv) {
                unmatched92 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1701_left, _1704_right));
                }
              }
            }
            if (unmatched92) {
              if (_source92.is_EuclidianMod) {
                unmatched92 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1701_left, _1704_right));
                }
              }
            }
            if (unmatched92) {
              Dafny.ISequence<Dafny.Rune> _1708_op = _source92.dtor_Passthrough_a0;
              unmatched92 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1708_op, _1701_left, _1704_right, _1695_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1703_recIdentsL, _1706_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1709_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1710_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1711_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1711_toTpe;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1712_path = _let_tmp_rhs57.dtor_path;
      Dafny.ISequence<DAST._IType> _1713_typeArgs = _let_tmp_rhs57.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs58 = _let_tmp_rhs57.dtor_kind;
      DAST._IType _1714_b = _let_tmp_rhs58.dtor_baseType;
      DAST._INewtypeRange _1715_range = _let_tmp_rhs58.dtor_range;
      bool _1716_erase = _let_tmp_rhs58.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1717___v114 = _let_tmp_rhs57.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1718___v115 = _let_tmp_rhs57.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1719___v116 = _let_tmp_rhs57.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1720_nativeToType;
      _1720_nativeToType = DCOMP.COMP.NewtypeRangeToRustType(_1715_range);
      if (object.Equals(_1710_fromTpe, _1714_b)) {
        RAST._IExpr _1721_recursiveGen;
        DCOMP._IOwnership _1722_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1723_recIdents;
        RAST._IExpr _out233;
        DCOMP._IOwnership _out234;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out235;
        (this).GenExpr(_1709_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out233, out _out234, out _out235);
        _1721_recursiveGen = _out233;
        _1722_recOwned = _out234;
        _1723_recIdents = _out235;
        readIdents = _1723_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source93 = _1720_nativeToType;
        bool unmatched93 = true;
        if (unmatched93) {
          if (_source93.is_Some) {
            RAST._IType _1724_v = _source93.dtor_value;
            unmatched93 = false;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1721_recursiveGen, RAST.Expr.create_ExprFromType(_1724_v)));
            RAST._IExpr _out236;
            DCOMP._IOwnership _out237;
            (this).FromOwned(r, expectedOwnership, out _out236, out _out237);
            r = _out236;
            resultingOwnership = _out237;
          }
        }
        if (unmatched93) {
          unmatched93 = false;
          if (_1716_erase) {
            r = _1721_recursiveGen;
          } else {
            RAST._IType _1725_rhsType;
            RAST._IType _out238;
            _out238 = (this).GenType(_1711_toTpe, DCOMP.GenTypeContext.InBinding());
            _1725_rhsType = _out238;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1725_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1721_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out239;
          DCOMP._IOwnership _out240;
          (this).FromOwnership(r, _1722_recOwned, expectedOwnership, out _out239, out _out240);
          r = _out239;
          resultingOwnership = _out240;
        }
      } else {
        if ((_1720_nativeToType).is_Some) {
          DAST._IType _source94 = _1710_fromTpe;
          bool unmatched94 = true;
          if (unmatched94) {
            if (_source94.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source94.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1726_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1727_range0 = kind1.dtor_range;
                bool _1728_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1729_attributes0 = resolved1.dtor_attributes;
                unmatched94 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1730_nativeFromType;
                  _1730_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1727_range0);
                  if ((_1730_nativeFromType).is_Some) {
                    RAST._IExpr _1731_recursiveGen;
                    DCOMP._IOwnership _1732_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1733_recIdents;
                    RAST._IExpr _out241;
                    DCOMP._IOwnership _out242;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out243;
                    (this).GenExpr(_1709_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out241, out _out242, out _out243);
                    _1731_recursiveGen = _out241;
                    _1732_recOwned = _out242;
                    _1733_recIdents = _out243;
                    RAST._IExpr _out244;
                    DCOMP._IOwnership _out245;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1731_recursiveGen, (_1720_nativeToType).dtor_value), _1732_recOwned, expectedOwnership, out _out244, out _out245);
                    r = _out244;
                    resultingOwnership = _out245;
                    readIdents = _1733_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched94) {
            unmatched94 = false;
          }
          if (object.Equals(_1710_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1734_recursiveGen;
            DCOMP._IOwnership _1735_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1736_recIdents;
            RAST._IExpr _out246;
            DCOMP._IOwnership _out247;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out248;
            (this).GenExpr(_1709_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out246, out _out247, out _out248);
            _1734_recursiveGen = _out246;
            _1735_recOwned = _out247;
            _1736_recIdents = _out248;
            RAST._IExpr _out249;
            DCOMP._IOwnership _out250;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1734_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1720_nativeToType).dtor_value), _1735_recOwned, expectedOwnership, out _out249, out _out250);
            r = _out249;
            resultingOwnership = _out250;
            readIdents = _1736_recIdents;
            return ;
          }
        }
        RAST._IExpr _out251;
        DCOMP._IOwnership _out252;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1709_expr, _1710_fromTpe, _1714_b), _1714_b, _1711_toTpe), selfIdent, env, expectedOwnership, out _out251, out _out252, out _out253);
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
      DAST._IExpression _1737_expr = _let_tmp_rhs59.dtor_value;
      DAST._IType _1738_fromTpe = _let_tmp_rhs59.dtor_from;
      DAST._IType _1739_toTpe = _let_tmp_rhs59.dtor_typ;
      DAST._IType _let_tmp_rhs60 = _1738_fromTpe;
      DAST._IResolvedType _let_tmp_rhs61 = _let_tmp_rhs60.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1740___v122 = _let_tmp_rhs61.dtor_path;
      Dafny.ISequence<DAST._IType> _1741___v123 = _let_tmp_rhs61.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs62 = _let_tmp_rhs61.dtor_kind;
      DAST._IType _1742_b = _let_tmp_rhs62.dtor_baseType;
      DAST._INewtypeRange _1743_range = _let_tmp_rhs62.dtor_range;
      bool _1744_erase = _let_tmp_rhs62.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1745_attributes = _let_tmp_rhs61.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1746___v124 = _let_tmp_rhs61.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1747___v125 = _let_tmp_rhs61.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1748_nativeFromType;
      _1748_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1743_range);
      if (object.Equals(_1742_b, _1739_toTpe)) {
        RAST._IExpr _1749_recursiveGen;
        DCOMP._IOwnership _1750_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1751_recIdents;
        RAST._IExpr _out254;
        DCOMP._IOwnership _out255;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out256;
        (this).GenExpr(_1737_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out254, out _out255, out _out256);
        _1749_recursiveGen = _out254;
        _1750_recOwned = _out255;
        _1751_recIdents = _out256;
        readIdents = _1751_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source95 = _1748_nativeFromType;
        bool unmatched95 = true;
        if (unmatched95) {
          if (_source95.is_Some) {
            RAST._IType _1752_v = _source95.dtor_value;
            unmatched95 = false;
            RAST._IType _1753_toTpeRust;
            RAST._IType _out257;
            _out257 = (this).GenType(_1739_toTpe, DCOMP.GenTypeContext.@default());
            _1753_toTpeRust = _out257;
            r = ((((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1753_toTpeRust))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1749_recursiveGen));
            RAST._IExpr _out258;
            DCOMP._IOwnership _out259;
            (this).FromOwned(r, expectedOwnership, out _out258, out _out259);
            r = _out258;
            resultingOwnership = _out259;
          }
        }
        if (unmatched95) {
          unmatched95 = false;
          if (_1744_erase) {
            r = _1749_recursiveGen;
          } else {
            r = (_1749_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out260;
          DCOMP._IOwnership _out261;
          (this).FromOwnership(r, _1750_recOwned, expectedOwnership, out _out260, out _out261);
          r = _out260;
          resultingOwnership = _out261;
        }
      } else {
        if ((_1748_nativeFromType).is_Some) {
          if (object.Equals(_1739_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1754_recursiveGen;
            DCOMP._IOwnership _1755_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1756_recIdents;
            RAST._IExpr _out262;
            DCOMP._IOwnership _out263;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out264;
            (this).GenExpr(_1737_expr, selfIdent, env, expectedOwnership, out _out262, out _out263, out _out264);
            _1754_recursiveGen = _out262;
            _1755_recOwned = _out263;
            _1756_recIdents = _out264;
            RAST._IExpr _out265;
            DCOMP._IOwnership _out266;
            (this).FromOwnership((((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).AsExpr()).Apply1(RAST.Expr.create_TypeAscription(_1754_recursiveGen, (this).DafnyCharUnderlying)), _1755_recOwned, expectedOwnership, out _out265, out _out266);
            r = _out265;
            resultingOwnership = _out266;
            readIdents = _1756_recIdents;
            return ;
          }
        }
        RAST._IExpr _out267;
        DCOMP._IOwnership _out268;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out269;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1737_expr, _1738_fromTpe, _1742_b), _1742_b, _1739_toTpe), selfIdent, env, expectedOwnership, out _out267, out _out268, out _out269);
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
        Std.Wrappers._IResult<__T, __E> _1757_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1757_valueOrError0).IsFailure()) {
          return (_1757_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1758_head = (_1757_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1759_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1759_valueOrError1).IsFailure()) {
            return (_1759_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1760_tail = (_1759_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1758_head), _1760_tail));
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
          RAST._IType _1761_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1762_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel((this).upcast)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1761_fromTpeUnderlying, _1762_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1763_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1763_valueOrError0).IsFailure()) {
          return (_1763_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1764_lambda = (_1763_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1764_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).AsExpr()).Apply1(_1764_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1765_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim12 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr12 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
          for (int i12 = 0; i12 < dim12; i12++) {
            var _1766_i = (BigInteger) i12;
            arr12[(int)(_1766_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_1766_i), ((fromTpe).dtor_arguments).Select(_1766_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_1766_i), ((toTpe).dtor_arguments).Select(_1766_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr12);
        }))());
        if ((_1765_valueOrError1).IsFailure()) {
          return (_1765_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1767_lambdas = (_1765_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim13 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr13 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
  for (int i13 = 0; i13 < dim13; i13++) {
    var _1768_i = (BigInteger) i13;
    arr13[(int)(_1768_i)] = ((fromTpe).dtor_arguments).Select(_1768_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr13);
}))())).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1767_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1769_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1770_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1771_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1772_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1773_valueOrError2 = (this).UpcastConversionLambda(_1771_newFromType, _1769_newFromTpe, _1772_newToType, _1770_newToTpe, typeParams);
        if ((_1773_valueOrError2).IsFailure()) {
          return (_1773_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1774_coerceArg = (_1773_valueOrError2).Extract();
          RAST._IPath _1775_collectionType = (RAST.__default.dafny__runtime).MSel(((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name);
          RAST._IExpr _1776_baseType = (((((((fromTpe).Expand()).dtor_baseName).dtor_path).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? (((_1775_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((((fromTpe).Expand()).dtor_arguments).Select(BigInteger.Zero), _1769_newFromTpe))) : (((_1775_collectionType).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1769_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1776_baseType).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1774_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1777_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1777_valueOrError3).IsFailure()) {
          return (_1777_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1778_lambda = (_1777_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1778_lambda));
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
      DAST._IExpression _1779_expr = _let_tmp_rhs63.dtor_value;
      DAST._IType _1780_fromTpe = _let_tmp_rhs63.dtor_from;
      DAST._IType _1781_toTpe = _let_tmp_rhs63.dtor_typ;
      RAST._IType _1782_fromTpeGen;
      RAST._IType _out270;
      _out270 = (this).GenType(_1780_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1782_fromTpeGen = _out270;
      RAST._IType _1783_toTpeGen;
      RAST._IType _out271;
      _out271 = (this).GenType(_1781_toTpe, DCOMP.GenTypeContext.InBinding());
      _1783_toTpeGen = _out271;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1784_upcastConverter;
      _1784_upcastConverter = (this).UpcastConversionLambda(_1780_fromTpe, _1782_fromTpeGen, _1781_toTpe, _1783_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1784_upcastConverter).is_Success) {
        RAST._IExpr _1785_conversionLambda;
        _1785_conversionLambda = (_1784_upcastConverter).dtor_value;
        RAST._IExpr _1786_recursiveGen;
        DCOMP._IOwnership _1787_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1788_recIdents;
        RAST._IExpr _out272;
        DCOMP._IOwnership _out273;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out274;
        (this).GenExpr(_1779_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out272, out _out273, out _out274);
        _1786_recursiveGen = _out272;
        _1787_recOwned = _out273;
        _1788_recIdents = _out274;
        readIdents = _1788_recIdents;
        r = (_1785_conversionLambda).Apply1(_1786_recursiveGen);
        RAST._IExpr _out275;
        DCOMP._IOwnership _out276;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out275, out _out276);
        r = _out275;
        resultingOwnership = _out276;
      } else if ((this).IsDowncastConversion(_1782_fromTpeGen, _1783_toTpeGen)) {
        RAST._IExpr _1789_recursiveGen;
        DCOMP._IOwnership _1790_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1791_recIdents;
        RAST._IExpr _out277;
        DCOMP._IOwnership _out278;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out279;
        (this).GenExpr(_1779_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out277, out _out278, out _out279);
        _1789_recursiveGen = _out277;
        _1790_recOwned = _out278;
        _1791_recIdents = _out279;
        readIdents = _1791_recIdents;
        _1783_toTpeGen = (_1783_toTpeGen).ObjectOrPointerUnderlying();
        r = (((RAST.__default.dafny__runtime).MSel((this).downcast)).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1789_recursiveGen, RAST.Expr.create_ExprFromType(_1783_toTpeGen)));
        RAST._IExpr _out280;
        DCOMP._IOwnership _out281;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out280, out _out281);
        r = _out280;
        resultingOwnership = _out281;
      } else {
        RAST._IExpr _1792_recursiveGen;
        DCOMP._IOwnership _1793_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1794_recIdents;
        RAST._IExpr _out282;
        DCOMP._IOwnership _out283;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out284;
        (this).GenExpr(_1779_expr, selfIdent, env, expectedOwnership, out _out282, out _out283, out _out284);
        _1792_recursiveGen = _out282;
        _1793_recOwned = _out283;
        _1794_recIdents = _out284;
        readIdents = _1794_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs64 = _1784_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs65 = _let_tmp_rhs64.dtor_error;
        DAST._IType _1795_fromType = _let_tmp_rhs65.dtor__0;
        RAST._IType _1796_fromTpeGen = _let_tmp_rhs65.dtor__1;
        DAST._IType _1797_toType = _let_tmp_rhs65.dtor__2;
        RAST._IType _1798_toTpeGen = _let_tmp_rhs65.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1799_m = _let_tmp_rhs65.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1800_msg;
        _1800_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1796_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1798_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1800_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1792_recursiveGen)._ToString(DCOMP.__default.IND), _1800_msg));
        RAST._IExpr _out285;
        DCOMP._IOwnership _out286;
        (this).FromOwnership(r, _1793_recOwned, expectedOwnership, out _out285, out _out286);
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
      DAST._IExpression _1801_expr = _let_tmp_rhs66.dtor_value;
      DAST._IType _1802_fromTpe = _let_tmp_rhs66.dtor_from;
      DAST._IType _1803_toTpe = _let_tmp_rhs66.dtor_typ;
      if (object.Equals(_1802_fromTpe, _1803_toTpe)) {
        RAST._IExpr _1804_recursiveGen;
        DCOMP._IOwnership _1805_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1806_recIdents;
        RAST._IExpr _out287;
        DCOMP._IOwnership _out288;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out289;
        (this).GenExpr(_1801_expr, selfIdent, env, expectedOwnership, out _out287, out _out288, out _out289);
        _1804_recursiveGen = _out287;
        _1805_recOwned = _out288;
        _1806_recIdents = _out289;
        r = _1804_recursiveGen;
        RAST._IExpr _out290;
        DCOMP._IOwnership _out291;
        (this).FromOwnership(r, _1805_recOwned, expectedOwnership, out _out290, out _out291);
        r = _out290;
        resultingOwnership = _out291;
        readIdents = _1806_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source96 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1802_fromTpe, _1803_toTpe);
        bool unmatched96 = true;
        if (unmatched96) {
          DAST._IType _10 = _source96.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1807_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1808_range = kind2.dtor_range;
              bool _1809_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1810_attributes = resolved2.dtor_attributes;
              unmatched96 = false;
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
        if (unmatched96) {
          DAST._IType _00 = _source96.dtor__0;
          if (_00.is_UserDefined) {
            DAST._IResolvedType resolved3 = _00.dtor_resolved;
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1811_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1812_range = kind3.dtor_range;
              bool _1813_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1814_attributes = resolved3.dtor_attributes;
              unmatched96 = false;
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
        if (unmatched96) {
          DAST._IType _01 = _source96.dtor__0;
          if (_01.is_Primitive) {
            DAST._IPrimitive _h72 = _01.dtor_Primitive_a0;
            if (_h72.is_Int) {
              DAST._IType _11 = _source96.dtor__1;
              if (_11.is_Primitive) {
                DAST._IPrimitive _h73 = _11.dtor_Primitive_a0;
                if (_h73.is_Real) {
                  unmatched96 = false;
                  {
                    RAST._IExpr _1815_recursiveGen;
                    DCOMP._IOwnership _1816___v136;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1817_recIdents;
                    RAST._IExpr _out298;
                    DCOMP._IOwnership _out299;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out300;
                    (this).GenExpr(_1801_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out298, out _out299, out _out300);
                    _1815_recursiveGen = _out298;
                    _1816___v136 = _out299;
                    _1817_recIdents = _out300;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1815_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out301;
                    DCOMP._IOwnership _out302;
                    (this).FromOwned(r, expectedOwnership, out _out301, out _out302);
                    r = _out301;
                    resultingOwnership = _out302;
                    readIdents = _1817_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched96) {
          DAST._IType _02 = _source96.dtor__0;
          if (_02.is_Primitive) {
            DAST._IPrimitive _h74 = _02.dtor_Primitive_a0;
            if (_h74.is_Real) {
              DAST._IType _12 = _source96.dtor__1;
              if (_12.is_Primitive) {
                DAST._IPrimitive _h75 = _12.dtor_Primitive_a0;
                if (_h75.is_Int) {
                  unmatched96 = false;
                  {
                    RAST._IExpr _1818_recursiveGen;
                    DCOMP._IOwnership _1819___v137;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1820_recIdents;
                    RAST._IExpr _out303;
                    DCOMP._IOwnership _out304;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out305;
                    (this).GenExpr(_1801_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out303, out _out304, out _out305);
                    _1818_recursiveGen = _out303;
                    _1819___v137 = _out304;
                    _1820_recIdents = _out305;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1818_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out306;
                    DCOMP._IOwnership _out307;
                    (this).FromOwned(r, expectedOwnership, out _out306, out _out307);
                    r = _out306;
                    resultingOwnership = _out307;
                    readIdents = _1820_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched96) {
          DAST._IType _03 = _source96.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h76 = _03.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _13 = _source96.dtor__1;
              if (_13.is_Passthrough) {
                unmatched96 = false;
                {
                  RAST._IType _1821_rhsType;
                  RAST._IType _out308;
                  _out308 = (this).GenType(_1803_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1821_rhsType = _out308;
                  RAST._IExpr _1822_recursiveGen;
                  DCOMP._IOwnership _1823___v139;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1824_recIdents;
                  RAST._IExpr _out309;
                  DCOMP._IOwnership _out310;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out311;
                  (this).GenExpr(_1801_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out309, out _out310, out _out311);
                  _1822_recursiveGen = _out309;
                  _1823___v139 = _out310;
                  _1824_recIdents = _out311;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1821_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1822_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out312;
                  DCOMP._IOwnership _out313;
                  (this).FromOwned(r, expectedOwnership, out _out312, out _out313);
                  r = _out312;
                  resultingOwnership = _out313;
                  readIdents = _1824_recIdents;
                }
              }
            }
          }
        }
        if (unmatched96) {
          DAST._IType _04 = _source96.dtor__0;
          if (_04.is_Passthrough) {
            DAST._IType _14 = _source96.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h77 = _14.dtor_Primitive_a0;
              if (_h77.is_Int) {
                unmatched96 = false;
                {
                  RAST._IType _1825_rhsType;
                  RAST._IType _out314;
                  _out314 = (this).GenType(_1802_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1825_rhsType = _out314;
                  RAST._IExpr _1826_recursiveGen;
                  DCOMP._IOwnership _1827___v141;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1828_recIdents;
                  RAST._IExpr _out315;
                  DCOMP._IOwnership _out316;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out317;
                  (this).GenExpr(_1801_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out315, out _out316, out _out317);
                  _1826_recursiveGen = _out315;
                  _1827___v141 = _out316;
                  _1828_recIdents = _out317;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1826_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out318;
                  DCOMP._IOwnership _out319;
                  (this).FromOwned(r, expectedOwnership, out _out318, out _out319);
                  r = _out318;
                  resultingOwnership = _out319;
                  readIdents = _1828_recIdents;
                }
              }
            }
          }
        }
        if (unmatched96) {
          DAST._IType _05 = _source96.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h78 = _05.dtor_Primitive_a0;
            if (_h78.is_Int) {
              DAST._IType _15 = _source96.dtor__1;
              if (_15.is_Primitive) {
                DAST._IPrimitive _h79 = _15.dtor_Primitive_a0;
                if (_h79.is_Char) {
                  unmatched96 = false;
                  {
                    RAST._IType _1829_rhsType;
                    RAST._IType _out320;
                    _out320 = (this).GenType(_1803_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1829_rhsType = _out320;
                    RAST._IExpr _1830_recursiveGen;
                    DCOMP._IOwnership _1831___v142;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1832_recIdents;
                    RAST._IExpr _out321;
                    DCOMP._IOwnership _out322;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out323;
                    (this).GenExpr(_1801_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out321, out _out322, out _out323);
                    _1830_recursiveGen = _out321;
                    _1831___v142 = _out322;
                    _1832_recIdents = _out323;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1830_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out324;
                    DCOMP._IOwnership _out325;
                    (this).FromOwned(r, expectedOwnership, out _out324, out _out325);
                    r = _out324;
                    resultingOwnership = _out325;
                    readIdents = _1832_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched96) {
          DAST._IType _06 = _source96.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h710 = _06.dtor_Primitive_a0;
            if (_h710.is_Char) {
              DAST._IType _16 = _source96.dtor__1;
              if (_16.is_Primitive) {
                DAST._IPrimitive _h711 = _16.dtor_Primitive_a0;
                if (_h711.is_Int) {
                  unmatched96 = false;
                  {
                    RAST._IType _1833_rhsType;
                    RAST._IType _out326;
                    _out326 = (this).GenType(_1802_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1833_rhsType = _out326;
                    RAST._IExpr _1834_recursiveGen;
                    DCOMP._IOwnership _1835___v143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1836_recIdents;
                    RAST._IExpr _out327;
                    DCOMP._IOwnership _out328;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out329;
                    (this).GenExpr(_1801_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out327, out _out328, out _out329);
                    _1834_recursiveGen = _out327;
                    _1835___v143 = _out328;
                    _1836_recIdents = _out329;
                    r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1((_1834_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out330;
                    DCOMP._IOwnership _out331;
                    (this).FromOwned(r, expectedOwnership, out _out330, out _out331);
                    r = _out330;
                    resultingOwnership = _out331;
                    readIdents = _1836_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched96) {
          DAST._IType _07 = _source96.dtor__0;
          if (_07.is_Passthrough) {
            DAST._IType _17 = _source96.dtor__1;
            if (_17.is_Passthrough) {
              unmatched96 = false;
              {
                RAST._IExpr _1837_recursiveGen;
                DCOMP._IOwnership _1838___v146;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1839_recIdents;
                RAST._IExpr _out332;
                DCOMP._IOwnership _out333;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out334;
                (this).GenExpr(_1801_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out332, out _out333, out _out334);
                _1837_recursiveGen = _out332;
                _1838___v146 = _out333;
                _1839_recIdents = _out334;
                RAST._IType _1840_toTpeGen;
                RAST._IType _out335;
                _out335 = (this).GenType(_1803_toTpe, DCOMP.GenTypeContext.InBinding());
                _1840_toTpeGen = _out335;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1837_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1840_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out336;
                DCOMP._IOwnership _out337;
                (this).FromOwned(r, expectedOwnership, out _out336, out _out337);
                r = _out336;
                resultingOwnership = _out337;
                readIdents = _1839_recIdents;
              }
            }
          }
        }
        if (unmatched96) {
          unmatched96 = false;
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
      Std.Wrappers._IOption<RAST._IType> _1841_tpe;
      _1841_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1842_placeboOpt;
      _1842_placeboOpt = (((_1841_tpe).is_Some) ? (((_1841_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1843_currentlyBorrowed;
      _1843_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1844_noNeedOfClone;
      _1844_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1842_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1843_currentlyBorrowed = false;
        _1844_noNeedOfClone = true;
        _1841_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1842_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_1843_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1841_tpe).is_Some) && (((_1841_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1845_needObjectFromRef;
        _1845_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source97 = (selfIdent).dtor_dafnyType;
          bool unmatched97 = true;
          if (unmatched97) {
            if (_source97.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source97.dtor_resolved;
              DAST._IResolvedTypeBase _1846_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1847_attributes = resolved4.dtor_attributes;
              unmatched97 = false;
              return ((_1846_base).is_Class) || ((_1846_base).is_Trait);
            }
          }
          if (unmatched97) {
            unmatched97 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_1845_needObjectFromRef) {
          r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1844_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1844_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1843_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1841_tpe).is_Some) && (((_1841_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1848_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1848_attributes).UniqueElements, false, (((_exists_var_1) => {
        DAST._IAttribute _1849_attribute = (DAST._IAttribute)_exists_var_1;
        return ((_1848_attributes).Contains(_1849_attribute)) && ((((_1849_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1849_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      Dafny.ISequence<DAST._IFormal> _1850_signature;
      _1850_signature = (((name).is_CallName) ? ((((((name).dtor_receiverArg).is_Some) && ((name).dtor_receiverAsArgument)) ? (Dafny.Sequence<DAST._IFormal>.Concat(Dafny.Sequence<DAST._IFormal>.FromElements(((name).dtor_receiverArg).dtor_value), ((name).dtor_signature))) : (((name).dtor_signature)))) : (Dafny.Sequence<DAST._IFormal>.FromElements()));
      BigInteger _hi37 = new BigInteger((args).Count);
      for (BigInteger _1851_i = BigInteger.Zero; _1851_i < _hi37; _1851_i++) {
        DCOMP._IOwnership _1852_argOwnership;
        _1852_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if ((_1851_i) < (new BigInteger((_1850_signature).Count))) {
          RAST._IType _1853_tpe;
          RAST._IType _out341;
          _out341 = (this).GenType(((_1850_signature).Select(_1851_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1853_tpe = _out341;
          if ((_1853_tpe).CanReadWithoutClone()) {
            _1852_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1854_argExpr;
        DCOMP._IOwnership _1855___v153;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1856_argIdents;
        RAST._IExpr _out342;
        DCOMP._IOwnership _out343;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out344;
        (this).GenExpr((args).Select(_1851_i), selfIdent, env, _1852_argOwnership, out _out342, out _out343, out _out344);
        _1854_argExpr = _out342;
        _1855___v153 = _out343;
        _1856_argIdents = _out344;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1854_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1856_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi38 = new BigInteger((typeArgs).Count);
      for (BigInteger _1857_typeI = BigInteger.Zero; _1857_typeI < _hi38; _1857_typeI++) {
        RAST._IType _1858_typeExpr;
        RAST._IType _out345;
        _out345 = (this).GenType((typeArgs).Select(_1857_typeI), DCOMP.GenTypeContext.@default());
        _1858_typeExpr = _out345;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1858_typeExpr));
      }
      DAST._ICallName _source98 = name;
      bool unmatched98 = true;
      if (unmatched98) {
        if (_source98.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _1859_nameIdent = _source98.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType1 = _source98.dtor_onType;
          if (onType1.is_Some) {
            DAST._IType value10 = onType1.dtor_value;
            if (value10.is_UserDefined) {
              DAST._IResolvedType _1860_resolvedType = value10.dtor_resolved;
              unmatched98 = false;
              if ((((_1860_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_1861_resolvedType, _1862_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.SingleValue<Dafny.ISequence<Dafny.Rune>>(_1862_nameIdent), true, (((_forall_var_8) => {
                Dafny.ISequence<Dafny.Rune> _1863_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                return !(((_1861_resolvedType).dtor_properMethods).Contains(_1863_m)) || (!object.Equals(_1863_m, _1862_nameIdent));
              }))))(_1860_resolvedType, _1859_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_1860_resolvedType, (_1859_nameIdent)), _1860_resolvedType));
              } else {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
              }
            }
          }
        }
      }
      if (unmatched98) {
        unmatched98 = false;
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
      if ((((((fullNameQualifier).is_Some) && ((selfIdent).is_ThisTyped)) && (((selfIdent).dtor_dafnyType).is_UserDefined)) && ((this).IsSameResolvedType(((selfIdent).dtor_dafnyType).dtor_resolved, (fullNameQualifier).dtor_value))) && (!((this).HasExternAttributeRenamingModule(((fullNameQualifier).dtor_value).dtor_attributes)))) {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    }
    public Dafny.ISequence<Dafny.Rune> GetMethodName(DAST._IExpression @on, DAST._ICallName name)
    {
      var _pat_let_tv144 = @on;
      DAST._ICallName _source99 = name;
      bool unmatched99 = true;
      if (unmatched99) {
        if (_source99.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _1864_ident = _source99.dtor_name;
          unmatched99 = false;
          if ((_pat_let_tv144).is_ExternCompanion) {
            return (_1864_ident);
          } else {
            return DCOMP.__default.escapeName(_1864_ident);
          }
        }
      }
      if (unmatched99) {
        bool disjunctiveMatch14 = false;
        if (_source99.is_MapBuilderAdd) {
          disjunctiveMatch14 = true;
        }
        if (_source99.is_SetBuilderAdd) {
          disjunctiveMatch14 = true;
        }
        if (disjunctiveMatch14) {
          unmatched99 = false;
          return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
        }
      }
      if (unmatched99) {
        bool disjunctiveMatch15 = false;
        disjunctiveMatch15 = true;
        disjunctiveMatch15 = true;
        if (disjunctiveMatch15) {
          unmatched99 = false;
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
      DAST._IExpression _source100 = e;
      bool unmatched100 = true;
      if (unmatched100) {
        if (_source100.is_Literal) {
          unmatched100 = false;
          RAST._IExpr _out346;
          DCOMP._IOwnership _out347;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out346, out _out347, out _out348);
          r = _out346;
          resultingOwnership = _out347;
          readIdents = _out348;
        }
      }
      if (unmatched100) {
        if (_source100.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1865_name = _source100.dtor_name;
          unmatched100 = false;
          {
            RAST._IExpr _out349;
            DCOMP._IOwnership _out350;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out351;
            (this).GenIdent(DCOMP.__default.escapeVar(_1865_name), selfIdent, env, expectedOwnership, out _out349, out _out350, out _out351);
            r = _out349;
            resultingOwnership = _out350;
            readIdents = _out351;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_ExternCompanion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1866_path = _source100.dtor_ExternCompanion_a0;
          unmatched100 = false;
          {
            RAST._IExpr _out352;
            _out352 = DCOMP.COMP.GenPathExpr(_1866_path, false);
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
      if (unmatched100) {
        if (_source100.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1867_path = _source100.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _1868_typeArgs = _source100.dtor_typeArgs;
          unmatched100 = false;
          {
            RAST._IExpr _out355;
            _out355 = DCOMP.COMP.GenPathExpr(_1867_path, true);
            r = _out355;
            if ((new BigInteger((_1868_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1869_typeExprs;
              _1869_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi39 = new BigInteger((_1868_typeArgs).Count);
              for (BigInteger _1870_i = BigInteger.Zero; _1870_i < _hi39; _1870_i++) {
                RAST._IType _1871_typeExpr;
                RAST._IType _out356;
                _out356 = (this).GenType((_1868_typeArgs).Select(_1870_i), DCOMP.GenTypeContext.@default());
                _1871_typeExpr = _out356;
                _1869_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1869_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1871_typeExpr));
              }
              r = (r).ApplyType(_1869_typeExprs);
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
      if (unmatched100) {
        if (_source100.is_InitializationValue) {
          DAST._IType _1872_typ = _source100.dtor_typ;
          unmatched100 = false;
          {
            RAST._IType _1873_typExpr;
            RAST._IType _out359;
            _out359 = (this).GenType(_1872_typ, DCOMP.GenTypeContext.@default());
            _1873_typExpr = _out359;
            if ((_1873_typExpr).IsObjectOrPointer()) {
              r = (_1873_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1873_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
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
      if (unmatched100) {
        if (_source100.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1874_values = _source100.dtor_Tuple_a0;
          unmatched100 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1875_exprs;
            _1875_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi40 = new BigInteger((_1874_values).Count);
            for (BigInteger _1876_i = BigInteger.Zero; _1876_i < _hi40; _1876_i++) {
              RAST._IExpr _1877_recursiveGen;
              DCOMP._IOwnership _1878___v163;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1879_recIdents;
              RAST._IExpr _out362;
              DCOMP._IOwnership _out363;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out364;
              (this).GenExpr((_1874_values).Select(_1876_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out362, out _out363, out _out364);
              _1877_recursiveGen = _out362;
              _1878___v163 = _out363;
              _1879_recIdents = _out364;
              _1875_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1875_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1877_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1879_recIdents);
            }
            r = (((new BigInteger((_1874_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1875_exprs)) : (RAST.__default.SystemTuple(_1875_exprs)));
            RAST._IExpr _out365;
            DCOMP._IOwnership _out366;
            (this).FromOwned(r, expectedOwnership, out _out365, out _out366);
            r = _out365;
            resultingOwnership = _out366;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1880_path = _source100.dtor_path;
          Dafny.ISequence<DAST._IType> _1881_typeArgs = _source100.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1882_args = _source100.dtor_args;
          unmatched100 = false;
          {
            RAST._IExpr _out367;
            _out367 = DCOMP.COMP.GenPathExpr(_1880_path, true);
            r = _out367;
            if ((new BigInteger((_1881_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1883_typeExprs;
              _1883_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi41 = new BigInteger((_1881_typeArgs).Count);
              for (BigInteger _1884_i = BigInteger.Zero; _1884_i < _hi41; _1884_i++) {
                RAST._IType _1885_typeExpr;
                RAST._IType _out368;
                _out368 = (this).GenType((_1881_typeArgs).Select(_1884_i), DCOMP.GenTypeContext.@default());
                _1885_typeExpr = _out368;
                _1883_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1883_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1885_typeExpr));
              }
              r = (r).ApplyType(_1883_typeExprs);
            }
            r = (r).FSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1886_arguments;
            _1886_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi42 = new BigInteger((_1882_args).Count);
            for (BigInteger _1887_i = BigInteger.Zero; _1887_i < _hi42; _1887_i++) {
              RAST._IExpr _1888_recursiveGen;
              DCOMP._IOwnership _1889___v164;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1890_recIdents;
              RAST._IExpr _out369;
              DCOMP._IOwnership _out370;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
              (this).GenExpr((_1882_args).Select(_1887_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out369, out _out370, out _out371);
              _1888_recursiveGen = _out369;
              _1889___v164 = _out370;
              _1890_recIdents = _out371;
              _1886_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1886_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1888_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1890_recIdents);
            }
            r = (r).Apply(_1886_arguments);
            RAST._IExpr _out372;
            DCOMP._IOwnership _out373;
            (this).FromOwned(r, expectedOwnership, out _out372, out _out373);
            r = _out372;
            resultingOwnership = _out373;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _1891_dims = _source100.dtor_dims;
          DAST._IType _1892_typ = _source100.dtor_typ;
          unmatched100 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1891_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1893_msg;
              _1893_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1893_msg);
              }
              r = RAST.Expr.create_RawExpr(_1893_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1894_typeGen;
              RAST._IType _out374;
              _out374 = (this).GenType(_1892_typ, DCOMP.GenTypeContext.@default());
              _1894_typeGen = _out374;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1895_dimExprs;
              _1895_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi43 = new BigInteger((_1891_dims).Count);
              for (BigInteger _1896_i = BigInteger.Zero; _1896_i < _hi43; _1896_i++) {
                RAST._IExpr _1897_recursiveGen;
                DCOMP._IOwnership _1898___v165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1899_recIdents;
                RAST._IExpr _out375;
                DCOMP._IOwnership _out376;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out377;
                (this).GenExpr((_1891_dims).Select(_1896_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out375, out _out376, out _out377);
                _1897_recursiveGen = _out375;
                _1898___v165 = _out376;
                _1899_recIdents = _out377;
                _1895_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1895_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_1897_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1899_recIdents);
              }
              if ((new BigInteger((_1891_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1900_class__name;
                _1900_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1891_dims).Count)));
                r = (((((RAST.__default.dafny__runtime).MSel(_1900_class__name)).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1894_typeGen))).FSel((this).placebos__usize)).Apply(_1895_dimExprs);
              } else {
                r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1894_typeGen))).Apply(_1895_dimExprs);
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
      if (unmatched100) {
        if (_source100.is_ArrayIndexToInt) {
          DAST._IExpression _1901_underlying = _source100.dtor_value;
          unmatched100 = false;
          {
            RAST._IExpr _1902_recursiveGen;
            DCOMP._IOwnership _1903___v166;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1904_recIdents;
            RAST._IExpr _out380;
            DCOMP._IOwnership _out381;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
            (this).GenExpr(_1901_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out380, out _out381, out _out382);
            _1902_recursiveGen = _out380;
            _1903___v166 = _out381;
            _1904_recIdents = _out382;
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(_1902_recursiveGen);
            readIdents = _1904_recIdents;
            RAST._IExpr _out383;
            DCOMP._IOwnership _out384;
            (this).FromOwned(r, expectedOwnership, out _out383, out _out384);
            r = _out383;
            resultingOwnership = _out384;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_FinalizeNewArray) {
          DAST._IExpression _1905_underlying = _source100.dtor_value;
          DAST._IType _1906_typ = _source100.dtor_typ;
          unmatched100 = false;
          {
            RAST._IType _1907_tpe;
            RAST._IType _out385;
            _out385 = (this).GenType(_1906_typ, DCOMP.GenTypeContext.@default());
            _1907_tpe = _out385;
            RAST._IExpr _1908_recursiveGen;
            DCOMP._IOwnership _1909___v167;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1910_recIdents;
            RAST._IExpr _out386;
            DCOMP._IOwnership _out387;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out388;
            (this).GenExpr(_1905_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out386, out _out387, out _out388);
            _1908_recursiveGen = _out386;
            _1909___v167 = _out387;
            _1910_recIdents = _out388;
            readIdents = _1910_recIdents;
            if ((_1907_tpe).IsObjectOrPointer()) {
              RAST._IType _1911_t;
              _1911_t = (_1907_tpe).ObjectOrPointerUnderlying();
              if ((_1911_t).is_Array) {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).AsExpr()).FSel((this).array__construct)).Apply1(_1908_recursiveGen);
              } else if ((_1911_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1912_c;
                _1912_c = (_1911_t).MultiArrayClass();
                r = ((((RAST.__default.dafny__runtime).MSel(_1912_c)).AsExpr()).FSel((this).array__construct)).Apply1(_1908_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1907_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1907_tpe)._ToString(DCOMP.__default.IND)));
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
      if (unmatched100) {
        if (_source100.is_DatatypeValue) {
          DAST._IResolvedType _1913_datatypeType = _source100.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1914_typeArgs = _source100.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1915_variant = _source100.dtor_variant;
          bool _1916_isCo = _source100.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1917_values = _source100.dtor_contents;
          unmatched100 = false;
          {
            RAST._IExpr _out391;
            _out391 = DCOMP.COMP.GenPathExpr((_1913_datatypeType).dtor_path, true);
            r = _out391;
            Dafny.ISequence<RAST._IType> _1918_genTypeArgs;
            _1918_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi44 = new BigInteger((_1914_typeArgs).Count);
            for (BigInteger _1919_i = BigInteger.Zero; _1919_i < _hi44; _1919_i++) {
              RAST._IType _1920_typeExpr;
              RAST._IType _out392;
              _out392 = (this).GenType((_1914_typeArgs).Select(_1919_i), DCOMP.GenTypeContext.@default());
              _1920_typeExpr = _out392;
              _1918_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1918_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1920_typeExpr));
            }
            if ((new BigInteger((_1914_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1918_genTypeArgs);
            }
            r = (r).FSel(DCOMP.__default.escapeName(_1915_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1921_assignments;
            _1921_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi45 = new BigInteger((_1917_values).Count);
            for (BigInteger _1922_i = BigInteger.Zero; _1922_i < _hi45; _1922_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs67 = (_1917_values).Select(_1922_i);
              Dafny.ISequence<Dafny.Rune> _1923_name = _let_tmp_rhs67.dtor__0;
              DAST._IExpression _1924_value = _let_tmp_rhs67.dtor__1;
              if (_1916_isCo) {
                RAST._IExpr _1925_recursiveGen;
                DCOMP._IOwnership _1926___v168;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1927_recIdents;
                RAST._IExpr _out393;
                DCOMP._IOwnership _out394;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out395;
                (this).GenExpr(_1924_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out393, out _out394, out _out395);
                _1925_recursiveGen = _out393;
                _1926___v168 = _out394;
                _1927_recIdents = _out395;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1927_recIdents);
                Dafny.ISequence<Dafny.Rune> _1928_allReadCloned;
                _1928_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1927_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1929_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1927_recIdents).Elements) {
                    _1929_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1927_recIdents).Contains(_1929_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4640)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1928_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1928_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1929_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1929_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1927_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1927_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1929_next));
                }
                Dafny.ISequence<Dafny.Rune> _1930_wasAssigned;
                _1930_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1928_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1925_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1921_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1921_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_1923_name), RAST.Expr.create_RawExpr(_1930_wasAssigned))));
              } else {
                RAST._IExpr _1931_recursiveGen;
                DCOMP._IOwnership _1932___v169;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1933_recIdents;
                RAST._IExpr _out396;
                DCOMP._IOwnership _out397;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out398;
                (this).GenExpr(_1924_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out396, out _out397, out _out398);
                _1931_recursiveGen = _out396;
                _1932___v169 = _out397;
                _1933_recIdents = _out398;
                _1921_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1921_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_1923_name), _1931_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1933_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1921_assignments);
            if ((this).IsRcWrapped((_1913_datatypeType).dtor_attributes)) {
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
      if (unmatched100) {
        if (_source100.is_Convert) {
          unmatched100 = false;
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
      if (unmatched100) {
        if (_source100.is_SeqConstruct) {
          DAST._IExpression _1934_length = _source100.dtor_length;
          DAST._IExpression _1935_expr = _source100.dtor_elem;
          unmatched100 = false;
          {
            RAST._IExpr _1936_recursiveGen;
            DCOMP._IOwnership _1937___v173;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1938_recIdents;
            RAST._IExpr _out404;
            DCOMP._IOwnership _out405;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out406;
            (this).GenExpr(_1935_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out404, out _out405, out _out406);
            _1936_recursiveGen = _out404;
            _1937___v173 = _out405;
            _1938_recIdents = _out406;
            RAST._IExpr _1939_lengthGen;
            DCOMP._IOwnership _1940___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1941_lengthIdents;
            RAST._IExpr _out407;
            DCOMP._IOwnership _out408;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
            (this).GenExpr(_1934_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out407, out _out408, out _out409);
            _1939_lengthGen = _out407;
            _1940___v174 = _out408;
            _1941_lengthIdents = _out409;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1936_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1939_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1938_recIdents, _1941_lengthIdents);
            RAST._IExpr _out410;
            DCOMP._IOwnership _out411;
            (this).FromOwned(r, expectedOwnership, out _out410, out _out411);
            r = _out410;
            resultingOwnership = _out411;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1942_exprs = _source100.dtor_elements;
          DAST._IType _1943_typ = _source100.dtor_typ;
          unmatched100 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1944_genTpe;
            RAST._IType _out412;
            _out412 = (this).GenType(_1943_typ, DCOMP.GenTypeContext.@default());
            _1944_genTpe = _out412;
            BigInteger _1945_i;
            _1945_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1946_args;
            _1946_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1945_i) < (new BigInteger((_1942_exprs).Count))) {
              RAST._IExpr _1947_recursiveGen;
              DCOMP._IOwnership _1948___v175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1949_recIdents;
              RAST._IExpr _out413;
              DCOMP._IOwnership _out414;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
              (this).GenExpr((_1942_exprs).Select(_1945_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out413, out _out414, out _out415);
              _1947_recursiveGen = _out413;
              _1948___v175 = _out414;
              _1949_recIdents = _out415;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1949_recIdents);
              _1946_args = Dafny.Sequence<RAST._IExpr>.Concat(_1946_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1947_recursiveGen));
              _1945_i = (_1945_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).AsExpr()).Apply(_1946_args);
            if ((new BigInteger((_1946_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).AsType()).Apply1(_1944_genTpe));
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
      if (unmatched100) {
        if (_source100.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1950_exprs = _source100.dtor_elements;
          unmatched100 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1951_generatedValues;
            _1951_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1952_i;
            _1952_i = BigInteger.Zero;
            while ((_1952_i) < (new BigInteger((_1950_exprs).Count))) {
              RAST._IExpr _1953_recursiveGen;
              DCOMP._IOwnership _1954___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1955_recIdents;
              RAST._IExpr _out418;
              DCOMP._IOwnership _out419;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out420;
              (this).GenExpr((_1950_exprs).Select(_1952_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out418, out _out419, out _out420);
              _1953_recursiveGen = _out418;
              _1954___v176 = _out419;
              _1955_recIdents = _out420;
              _1951_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1951_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1953_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1955_recIdents);
              _1952_i = (_1952_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).AsExpr()).Apply(_1951_generatedValues);
            RAST._IExpr _out421;
            DCOMP._IOwnership _out422;
            (this).FromOwned(r, expectedOwnership, out _out421, out _out422);
            r = _out421;
            resultingOwnership = _out422;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1956_exprs = _source100.dtor_elements;
          unmatched100 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1957_generatedValues;
            _1957_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1958_i;
            _1958_i = BigInteger.Zero;
            while ((_1958_i) < (new BigInteger((_1956_exprs).Count))) {
              RAST._IExpr _1959_recursiveGen;
              DCOMP._IOwnership _1960___v177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1961_recIdents;
              RAST._IExpr _out423;
              DCOMP._IOwnership _out424;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out425;
              (this).GenExpr((_1956_exprs).Select(_1958_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out423, out _out424, out _out425);
              _1959_recursiveGen = _out423;
              _1960___v177 = _out424;
              _1961_recIdents = _out425;
              _1957_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1957_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1959_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1961_recIdents);
              _1958_i = (_1958_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).AsExpr()).Apply(_1957_generatedValues);
            RAST._IExpr _out426;
            DCOMP._IOwnership _out427;
            (this).FromOwned(r, expectedOwnership, out _out426, out _out427);
            r = _out426;
            resultingOwnership = _out427;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_ToMultiset) {
          DAST._IExpression _1962_expr = _source100.dtor_ToMultiset_a0;
          unmatched100 = false;
          {
            RAST._IExpr _1963_recursiveGen;
            DCOMP._IOwnership _1964___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1965_recIdents;
            RAST._IExpr _out428;
            DCOMP._IOwnership _out429;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out430;
            (this).GenExpr(_1962_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out428, out _out429, out _out430);
            _1963_recursiveGen = _out428;
            _1964___v178 = _out429;
            _1965_recIdents = _out430;
            r = ((_1963_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1965_recIdents;
            RAST._IExpr _out431;
            DCOMP._IOwnership _out432;
            (this).FromOwned(r, expectedOwnership, out _out431, out _out432);
            r = _out431;
            resultingOwnership = _out432;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1966_mapElems = _source100.dtor_mapElems;
          unmatched100 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1967_generatedValues;
            _1967_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1968_i;
            _1968_i = BigInteger.Zero;
            while ((_1968_i) < (new BigInteger((_1966_mapElems).Count))) {
              RAST._IExpr _1969_recursiveGenKey;
              DCOMP._IOwnership _1970___v179;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1971_recIdentsKey;
              RAST._IExpr _out433;
              DCOMP._IOwnership _out434;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out435;
              (this).GenExpr(((_1966_mapElems).Select(_1968_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out433, out _out434, out _out435);
              _1969_recursiveGenKey = _out433;
              _1970___v179 = _out434;
              _1971_recIdentsKey = _out435;
              RAST._IExpr _1972_recursiveGenValue;
              DCOMP._IOwnership _1973___v180;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1974_recIdentsValue;
              RAST._IExpr _out436;
              DCOMP._IOwnership _out437;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out438;
              (this).GenExpr(((_1966_mapElems).Select(_1968_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out436, out _out437, out _out438);
              _1972_recursiveGenValue = _out436;
              _1973___v180 = _out437;
              _1974_recIdentsValue = _out438;
              _1967_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1967_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1969_recursiveGenKey, _1972_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1971_recIdentsKey), _1974_recIdentsValue);
              _1968_i = (_1968_i) + (BigInteger.One);
            }
            _1968_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1975_arguments;
            _1975_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1968_i) < (new BigInteger((_1967_generatedValues).Count))) {
              RAST._IExpr _1976_genKey;
              _1976_genKey = ((_1967_generatedValues).Select(_1968_i)).dtor__0;
              RAST._IExpr _1977_genValue;
              _1977_genValue = ((_1967_generatedValues).Select(_1968_i)).dtor__1;
              _1975_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1975_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1976_genKey, _1977_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1968_i = (_1968_i) + (BigInteger.One);
            }
            r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).AsExpr()).Apply(_1975_arguments);
            RAST._IExpr _out439;
            DCOMP._IOwnership _out440;
            (this).FromOwned(r, expectedOwnership, out _out439, out _out440);
            r = _out439;
            resultingOwnership = _out440;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_SeqUpdate) {
          DAST._IExpression _1978_expr = _source100.dtor_expr;
          DAST._IExpression _1979_index = _source100.dtor_indexExpr;
          DAST._IExpression _1980_value = _source100.dtor_value;
          unmatched100 = false;
          {
            RAST._IExpr _1981_exprR;
            DCOMP._IOwnership _1982___v181;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1983_exprIdents;
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
            (this).GenExpr(_1978_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out441, out _out442, out _out443);
            _1981_exprR = _out441;
            _1982___v181 = _out442;
            _1983_exprIdents = _out443;
            RAST._IExpr _1984_indexR;
            DCOMP._IOwnership _1985_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1986_indexIdents;
            RAST._IExpr _out444;
            DCOMP._IOwnership _out445;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out446;
            (this).GenExpr(_1979_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out444, out _out445, out _out446);
            _1984_indexR = _out444;
            _1985_indexOwnership = _out445;
            _1986_indexIdents = _out446;
            RAST._IExpr _1987_valueR;
            DCOMP._IOwnership _1988_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1989_valueIdents;
            RAST._IExpr _out447;
            DCOMP._IOwnership _out448;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out449;
            (this).GenExpr(_1980_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out447, out _out448, out _out449);
            _1987_valueR = _out447;
            _1988_valueOwnership = _out448;
            _1989_valueIdents = _out449;
            r = ((_1981_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1984_indexR, _1987_valueR));
            RAST._IExpr _out450;
            DCOMP._IOwnership _out451;
            (this).FromOwned(r, expectedOwnership, out _out450, out _out451);
            r = _out450;
            resultingOwnership = _out451;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1983_exprIdents, _1986_indexIdents), _1989_valueIdents);
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MapUpdate) {
          DAST._IExpression _1990_expr = _source100.dtor_expr;
          DAST._IExpression _1991_index = _source100.dtor_indexExpr;
          DAST._IExpression _1992_value = _source100.dtor_value;
          unmatched100 = false;
          {
            RAST._IExpr _1993_exprR;
            DCOMP._IOwnership _1994___v182;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1995_exprIdents;
            RAST._IExpr _out452;
            DCOMP._IOwnership _out453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
            (this).GenExpr(_1990_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out452, out _out453, out _out454);
            _1993_exprR = _out452;
            _1994___v182 = _out453;
            _1995_exprIdents = _out454;
            RAST._IExpr _1996_indexR;
            DCOMP._IOwnership _1997_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1998_indexIdents;
            RAST._IExpr _out455;
            DCOMP._IOwnership _out456;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out457;
            (this).GenExpr(_1991_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out455, out _out456, out _out457);
            _1996_indexR = _out455;
            _1997_indexOwnership = _out456;
            _1998_indexIdents = _out457;
            RAST._IExpr _1999_valueR;
            DCOMP._IOwnership _2000_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2001_valueIdents;
            RAST._IExpr _out458;
            DCOMP._IOwnership _out459;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out460;
            (this).GenExpr(_1992_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out458, out _out459, out _out460);
            _1999_valueR = _out458;
            _2000_valueOwnership = _out459;
            _2001_valueIdents = _out460;
            r = ((_1993_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1996_indexR, _1999_valueR));
            RAST._IExpr _out461;
            DCOMP._IOwnership _out462;
            (this).FromOwned(r, expectedOwnership, out _out461, out _out462);
            r = _out461;
            resultingOwnership = _out462;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1995_exprIdents, _1998_indexIdents), _2001_valueIdents);
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_This) {
          unmatched100 = false;
          {
            DCOMP._ISelfInfo _source101 = selfIdent;
            bool unmatched101 = true;
            if (unmatched101) {
              if (_source101.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _2002_id = _source101.dtor_rSelfName;
                DAST._IType _2003_dafnyType = _source101.dtor_dafnyType;
                unmatched101 = false;
                {
                  RAST._IExpr _out463;
                  DCOMP._IOwnership _out464;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out465;
                  (this).GenIdent(_2002_id, selfIdent, env, expectedOwnership, out _out463, out _out464, out _out465);
                  r = _out463;
                  resultingOwnership = _out464;
                  readIdents = _out465;
                }
              }
            }
            if (unmatched101) {
              DCOMP._ISelfInfo _2004_None = _source101;
              unmatched101 = false;
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
      if (unmatched100) {
        if (_source100.is_Ite) {
          DAST._IExpression _2005_cond = _source100.dtor_cond;
          DAST._IExpression _2006_t = _source100.dtor_thn;
          DAST._IExpression _2007_f = _source100.dtor_els;
          unmatched100 = false;
          {
            RAST._IExpr _2008_cond;
            DCOMP._IOwnership _2009___v183;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2010_recIdentsCond;
            RAST._IExpr _out468;
            DCOMP._IOwnership _out469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out470;
            (this).GenExpr(_2005_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out468, out _out469, out _out470);
            _2008_cond = _out468;
            _2009___v183 = _out469;
            _2010_recIdentsCond = _out470;
            RAST._IExpr _2011_fExpr;
            DCOMP._IOwnership _2012_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2013_recIdentsF;
            RAST._IExpr _out471;
            DCOMP._IOwnership _out472;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out473;
            (this).GenExpr(_2007_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out471, out _out472, out _out473);
            _2011_fExpr = _out471;
            _2012_fOwned = _out472;
            _2013_recIdentsF = _out473;
            RAST._IExpr _2014_tExpr;
            DCOMP._IOwnership _2015___v184;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2016_recIdentsT;
            RAST._IExpr _out474;
            DCOMP._IOwnership _out475;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out476;
            (this).GenExpr(_2006_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out474, out _out475, out _out476);
            _2014_tExpr = _out474;
            _2015___v184 = _out475;
            _2016_recIdentsT = _out476;
            r = RAST.Expr.create_IfExpr(_2008_cond, _2014_tExpr, _2011_fExpr);
            RAST._IExpr _out477;
            DCOMP._IOwnership _out478;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out477, out _out478);
            r = _out477;
            resultingOwnership = _out478;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2010_recIdentsCond, _2016_recIdentsT), _2013_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source100.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _2017_e = _source100.dtor_expr;
            DAST.Format._IUnaryOpFormat _2018_format = _source100.dtor_format1;
            unmatched100 = false;
            {
              RAST._IExpr _2019_recursiveGen;
              DCOMP._IOwnership _2020___v185;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2021_recIdents;
              RAST._IExpr _out479;
              DCOMP._IOwnership _out480;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out481;
              (this).GenExpr(_2017_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out479, out _out480, out _out481);
              _2019_recursiveGen = _out479;
              _2020___v185 = _out480;
              _2021_recIdents = _out481;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _2019_recursiveGen, _2018_format);
              RAST._IExpr _out482;
              DCOMP._IOwnership _out483;
              (this).FromOwned(r, expectedOwnership, out _out482, out _out483);
              r = _out482;
              resultingOwnership = _out483;
              readIdents = _2021_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source100.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _2022_e = _source100.dtor_expr;
            DAST.Format._IUnaryOpFormat _2023_format = _source100.dtor_format1;
            unmatched100 = false;
            {
              RAST._IExpr _2024_recursiveGen;
              DCOMP._IOwnership _2025___v186;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2026_recIdents;
              RAST._IExpr _out484;
              DCOMP._IOwnership _out485;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out486;
              (this).GenExpr(_2022_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out484, out _out485, out _out486);
              _2024_recursiveGen = _out484;
              _2025___v186 = _out485;
              _2026_recIdents = _out486;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _2024_recursiveGen, _2023_format);
              RAST._IExpr _out487;
              DCOMP._IOwnership _out488;
              (this).FromOwned(r, expectedOwnership, out _out487, out _out488);
              r = _out487;
              resultingOwnership = _out488;
              readIdents = _2026_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source100.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _2027_e = _source100.dtor_expr;
            DAST.Format._IUnaryOpFormat _2028_format = _source100.dtor_format1;
            unmatched100 = false;
            {
              RAST._IExpr _2029_recursiveGen;
              DCOMP._IOwnership _2030_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2031_recIdents;
              RAST._IExpr _out489;
              DCOMP._IOwnership _out490;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out491;
              (this).GenExpr(_2027_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out489, out _out490, out _out491);
              _2029_recursiveGen = _out489;
              _2030_recOwned = _out490;
              _2031_recIdents = _out491;
              r = ((_2029_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out492;
              DCOMP._IOwnership _out493;
              (this).FromOwned(r, expectedOwnership, out _out492, out _out493);
              r = _out492;
              resultingOwnership = _out493;
              readIdents = _2031_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_BinOp) {
          unmatched100 = false;
          RAST._IExpr _out494;
          DCOMP._IOwnership _out495;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out496;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out494, out _out495, out _out496);
          r = _out494;
          resultingOwnership = _out495;
          readIdents = _out496;
        }
      }
      if (unmatched100) {
        if (_source100.is_ArrayLen) {
          DAST._IExpression _2032_expr = _source100.dtor_expr;
          DAST._IType _2033_exprType = _source100.dtor_exprType;
          BigInteger _2034_dim = _source100.dtor_dim;
          bool _2035_native = _source100.dtor_native;
          unmatched100 = false;
          {
            RAST._IExpr _2036_recursiveGen;
            DCOMP._IOwnership _2037___v191;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2038_recIdents;
            RAST._IExpr _out497;
            DCOMP._IOwnership _out498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
            (this).GenExpr(_2032_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out497, out _out498, out _out499);
            _2036_recursiveGen = _out497;
            _2037___v191 = _out498;
            _2038_recIdents = _out499;
            RAST._IType _2039_arrayType;
            RAST._IType _out500;
            _out500 = (this).GenType(_2033_exprType, DCOMP.GenTypeContext.@default());
            _2039_arrayType = _out500;
            if (!((_2039_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2040_msg;
              _2040_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2039_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2040_msg);
              r = RAST.Expr.create_RawExpr(_2040_msg);
            } else {
              RAST._IType _2041_underlying;
              _2041_underlying = (_2039_arrayType).ObjectOrPointerUnderlying();
              if (((_2034_dim).Sign == 0) && ((_2041_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2036_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2034_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2036_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_2036_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_2034_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_2035_native)) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).AsExpr()).Apply1(r);
              }
            }
            RAST._IExpr _out501;
            DCOMP._IOwnership _out502;
            (this).FromOwned(r, expectedOwnership, out _out501, out _out502);
            r = _out501;
            resultingOwnership = _out502;
            readIdents = _2038_recIdents;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MapKeys) {
          DAST._IExpression _2042_expr = _source100.dtor_expr;
          unmatched100 = false;
          {
            RAST._IExpr _2043_recursiveGen;
            DCOMP._IOwnership _2044___v192;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2045_recIdents;
            RAST._IExpr _out503;
            DCOMP._IOwnership _out504;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
            (this).GenExpr(_2042_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out503, out _out504, out _out505);
            _2043_recursiveGen = _out503;
            _2044___v192 = _out504;
            _2045_recIdents = _out505;
            readIdents = _2045_recIdents;
            r = ((_2043_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out506;
            DCOMP._IOwnership _out507;
            (this).FromOwned(r, expectedOwnership, out _out506, out _out507);
            r = _out506;
            resultingOwnership = _out507;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MapValues) {
          DAST._IExpression _2046_expr = _source100.dtor_expr;
          unmatched100 = false;
          {
            RAST._IExpr _2047_recursiveGen;
            DCOMP._IOwnership _2048___v193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2049_recIdents;
            RAST._IExpr _out508;
            DCOMP._IOwnership _out509;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out510;
            (this).GenExpr(_2046_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out508, out _out509, out _out510);
            _2047_recursiveGen = _out508;
            _2048___v193 = _out509;
            _2049_recIdents = _out510;
            readIdents = _2049_recIdents;
            r = ((_2047_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out511;
            DCOMP._IOwnership _out512;
            (this).FromOwned(r, expectedOwnership, out _out511, out _out512);
            r = _out511;
            resultingOwnership = _out512;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MapItems) {
          DAST._IExpression _2050_expr = _source100.dtor_expr;
          unmatched100 = false;
          {
            RAST._IExpr _2051_recursiveGen;
            DCOMP._IOwnership _2052___v194;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2053_recIdents;
            RAST._IExpr _out513;
            DCOMP._IOwnership _out514;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out515;
            (this).GenExpr(_2050_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out513, out _out514, out _out515);
            _2051_recursiveGen = _out513;
            _2052___v194 = _out514;
            _2053_recIdents = _out515;
            readIdents = _2053_recIdents;
            r = ((_2051_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("items"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out516;
            DCOMP._IOwnership _out517;
            (this).FromOwned(r, expectedOwnership, out _out516, out _out517);
            r = _out516;
            resultingOwnership = _out517;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_SelectFn) {
          DAST._IExpression _2054_on = _source100.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2055_field = _source100.dtor_field;
          bool _2056_isDatatype = _source100.dtor_onDatatype;
          bool _2057_isStatic = _source100.dtor_isStatic;
          bool _2058_isConstant = _source100.dtor_isConstant;
          Dafny.ISequence<DAST._IType> _2059_arguments = _source100.dtor_arguments;
          unmatched100 = false;
          {
            RAST._IExpr _2060_onExpr;
            DCOMP._IOwnership _2061_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2062_recIdents;
            RAST._IExpr _out518;
            DCOMP._IOwnership _out519;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out520;
            (this).GenExpr(_2054_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out518, out _out519, out _out520);
            _2060_onExpr = _out518;
            _2061_onOwned = _out519;
            _2062_recIdents = _out520;
            Dafny.ISequence<Dafny.Rune> _2063_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2064_onString;
            _2064_onString = (_2060_onExpr)._ToString(DCOMP.__default.IND);
            if (_2057_isStatic) {
              DCOMP._IEnvironment _2065_lEnv;
              _2065_lEnv = env;
              Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>> _2066_args;
              _2066_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements();
              _2063_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|");
              BigInteger _hi46 = new BigInteger((_2059_arguments).Count);
              for (BigInteger _2067_i = BigInteger.Zero; _2067_i < _hi46; _2067_i++) {
                if ((_2067_i).Sign == 1) {
                  _2063_s = Dafny.Sequence<Dafny.Rune>.Concat(_2063_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                RAST._IType _2068_ty;
                RAST._IType _out521;
                _out521 = (this).GenType((_2059_arguments).Select(_2067_i), DCOMP.GenTypeContext.@default());
                _2068_ty = _out521;
                RAST._IType _2069_bTy;
                _2069_bTy = RAST.Type.create_Borrowed(_2068_ty);
                Dafny.ISequence<Dafny.Rune> _2070_name;
                _2070_name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), Std.Strings.__default.OfInt(_2067_i));
                _2065_lEnv = (_2065_lEnv).AddAssigned(_2070_name, _2069_bTy);
                _2066_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.Concat(_2066_args, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>.create(_2070_name, _2068_ty)));
                _2063_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2063_s, _2070_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_2069_bTy)._ToString(DCOMP.__default.IND));
              }
              _2063_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2063_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| ")), _2064_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeVar(_2055_field)), ((_2058_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("));
              BigInteger _hi47 = new BigInteger((_2066_args).Count);
              for (BigInteger _2071_i = BigInteger.Zero; _2071_i < _hi47; _2071_i++) {
                if ((_2071_i).Sign == 1) {
                  _2063_s = Dafny.Sequence<Dafny.Rune>.Concat(_2063_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType> _let_tmp_rhs68 = (_2066_args).Select(_2071_i);
                Dafny.ISequence<Dafny.Rune> _2072_name = _let_tmp_rhs68.dtor__0;
                RAST._IType _2073_ty = _let_tmp_rhs68.dtor__1;
                RAST._IExpr _2074_rIdent;
                DCOMP._IOwnership _2075___v195;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2076___v196;
                RAST._IExpr _out522;
                DCOMP._IOwnership _out523;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out524;
                (this).GenIdent(_2072_name, selfIdent, _2065_lEnv, (((_2073_ty).CanReadWithoutClone()) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed())), out _out522, out _out523, out _out524);
                _2074_rIdent = _out522;
                _2075___v195 = _out523;
                _2076___v196 = _out524;
                _2063_s = Dafny.Sequence<Dafny.Rune>.Concat(_2063_s, (_2074_rIdent)._ToString(DCOMP.__default.IND));
              }
              _2063_s = Dafny.Sequence<Dafny.Rune>.Concat(_2063_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            } else {
              _2063_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2063_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2063_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2064_onString), ((object.Equals(_2061_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2077_args;
              _2077_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2078_i;
              _2078_i = BigInteger.Zero;
              while ((_2078_i) < (new BigInteger((_2059_arguments).Count))) {
                if ((_2078_i).Sign == 1) {
                  _2077_args = Dafny.Sequence<Dafny.Rune>.Concat(_2077_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2077_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2077_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2078_i));
                _2078_i = (_2078_i) + (BigInteger.One);
              }
              _2063_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2063_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2077_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2063_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2063_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeVar(_2055_field)), ((_2058_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2077_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2063_s = Dafny.Sequence<Dafny.Rune>.Concat(_2063_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2063_s = Dafny.Sequence<Dafny.Rune>.Concat(_2063_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2079_typeShape;
            _2079_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2080_i;
            _2080_i = BigInteger.Zero;
            while ((_2080_i) < (new BigInteger((_2059_arguments).Count))) {
              if ((_2080_i).Sign == 1) {
                _2079_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2079_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2079_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2079_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2080_i = (_2080_i) + (BigInteger.One);
            }
            _2079_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2079_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2063_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2063_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2079_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2063_s);
            RAST._IExpr _out525;
            DCOMP._IOwnership _out526;
            (this).FromOwned(r, expectedOwnership, out _out525, out _out526);
            r = _out525;
            resultingOwnership = _out526;
            readIdents = _2062_recIdents;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_Select) {
          DAST._IExpression _2081_on = _source100.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2082_field = _source100.dtor_field;
          bool _2083_isConstant = _source100.dtor_isConstant;
          bool _2084_isDatatype = _source100.dtor_onDatatype;
          DAST._IType _2085_fieldType = _source100.dtor_fieldType;
          unmatched100 = false;
          {
            if (((_2081_on).is_Companion) || ((_2081_on).is_ExternCompanion)) {
              RAST._IExpr _2086_onExpr;
              DCOMP._IOwnership _2087_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2088_recIdents;
              RAST._IExpr _out527;
              DCOMP._IOwnership _out528;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
              (this).GenExpr(_2081_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out527, out _out528, out _out529);
              _2086_onExpr = _out527;
              _2087_onOwned = _out528;
              _2088_recIdents = _out529;
              r = ((_2086_onExpr).FSel(DCOMP.__default.escapeVar(_2082_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out530;
              DCOMP._IOwnership _out531;
              (this).FromOwned(r, expectedOwnership, out _out530, out _out531);
              r = _out530;
              resultingOwnership = _out531;
              readIdents = _2088_recIdents;
              return ;
            } else if (_2084_isDatatype) {
              RAST._IExpr _2089_onExpr;
              DCOMP._IOwnership _2090_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2091_recIdents;
              RAST._IExpr _out532;
              DCOMP._IOwnership _out533;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out534;
              (this).GenExpr(_2081_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out532, out _out533, out _out534);
              _2089_onExpr = _out532;
              _2090_onOwned = _out533;
              _2091_recIdents = _out534;
              r = ((_2089_onExpr).Sel(DCOMP.__default.escapeVar(_2082_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2092_typ;
              RAST._IType _out535;
              _out535 = (this).GenType(_2085_fieldType, DCOMP.GenTypeContext.@default());
              _2092_typ = _out535;
              RAST._IExpr _out536;
              DCOMP._IOwnership _out537;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out536, out _out537);
              r = _out536;
              resultingOwnership = _out537;
              readIdents = _2091_recIdents;
            } else {
              RAST._IExpr _2093_onExpr;
              DCOMP._IOwnership _2094_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2095_recIdents;
              RAST._IExpr _out538;
              DCOMP._IOwnership _out539;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out540;
              (this).GenExpr(_2081_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out538, out _out539, out _out540);
              _2093_onExpr = _out538;
              _2094_onOwned = _out539;
              _2095_recIdents = _out540;
              r = _2093_onExpr;
              if (!object.Equals(_2093_onExpr, RAST.__default.self)) {
                RAST._IExpr _source102 = _2093_onExpr;
                bool unmatched102 = true;
                if (unmatched102) {
                  if (_source102.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source102.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source102.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name8 = underlying5.dtor_name;
                        if (object.Equals(name8, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          unmatched102 = false;
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                        }
                      }
                    }
                  }
                }
                if (unmatched102) {
                  unmatched102 = false;
                }
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeVar(_2082_field));
              if (_2083_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out541;
              DCOMP._IOwnership _out542;
              (this).FromOwned(r, expectedOwnership, out _out541, out _out542);
              r = _out541;
              resultingOwnership = _out542;
              readIdents = _2095_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_Index) {
          DAST._IExpression _2096_on = _source100.dtor_expr;
          DAST._ICollKind _2097_collKind = _source100.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2098_indices = _source100.dtor_indices;
          unmatched100 = false;
          {
            RAST._IExpr _2099_onExpr;
            DCOMP._IOwnership _2100_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2101_recIdents;
            RAST._IExpr _out543;
            DCOMP._IOwnership _out544;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out545;
            (this).GenExpr(_2096_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out543, out _out544, out _out545);
            _2099_onExpr = _out543;
            _2100_onOwned = _out544;
            _2101_recIdents = _out545;
            readIdents = _2101_recIdents;
            r = _2099_onExpr;
            bool _2102_hadArray;
            _2102_hadArray = false;
            if (object.Equals(_2097_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2102_hadArray = true;
              if ((new BigInteger((_2098_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi48 = new BigInteger((_2098_indices).Count);
            for (BigInteger _2103_i = BigInteger.Zero; _2103_i < _hi48; _2103_i++) {
              if (object.Equals(_2097_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2104_idx;
                DCOMP._IOwnership _2105_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2106_recIdentsIdx;
                RAST._IExpr _out546;
                DCOMP._IOwnership _out547;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out548;
                (this).GenExpr((_2098_indices).Select(_2103_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out546, out _out547, out _out548);
                _2104_idx = _out546;
                _2105_idxOwned = _out547;
                _2106_recIdentsIdx = _out548;
                _2104_idx = RAST.__default.IntoUsize(_2104_idx);
                r = RAST.Expr.create_SelectIndex(r, _2104_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2106_recIdentsIdx);
              } else {
                RAST._IExpr _2107_idx;
                DCOMP._IOwnership _2108_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2109_recIdentsIdx;
                RAST._IExpr _out549;
                DCOMP._IOwnership _out550;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out551;
                (this).GenExpr((_2098_indices).Select(_2103_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out549, out _out550, out _out551);
                _2107_idx = _out549;
                _2108_idxOwned = _out550;
                _2109_recIdentsIdx = _out551;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2107_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2109_recIdentsIdx);
              }
            }
            if (_2102_hadArray) {
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
      if (unmatched100) {
        if (_source100.is_IndexRange) {
          DAST._IExpression _2110_on = _source100.dtor_expr;
          bool _2111_isArray = _source100.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2112_low = _source100.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2113_high = _source100.dtor_high;
          unmatched100 = false;
          {
            RAST._IExpr _2114_onExpr;
            DCOMP._IOwnership _2115_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2116_recIdents;
            RAST._IExpr _out554;
            DCOMP._IOwnership _out555;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out556;
            (this).GenExpr(_2110_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out554, out _out555, out _out556);
            _2114_onExpr = _out554;
            _2115_onOwned = _out555;
            _2116_recIdents = _out556;
            readIdents = _2116_recIdents;
            Dafny.ISequence<Dafny.Rune> _2117_methodName;
            _2117_methodName = (((_2112_low).is_Some) ? ((((_2113_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2113_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2118_arguments;
            _2118_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source103 = _2112_low;
            bool unmatched103 = true;
            if (unmatched103) {
              if (_source103.is_Some) {
                DAST._IExpression _2119_l = _source103.dtor_value;
                unmatched103 = false;
                {
                  RAST._IExpr _2120_lExpr;
                  DCOMP._IOwnership _2121___v199;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2122_recIdentsL;
                  RAST._IExpr _out557;
                  DCOMP._IOwnership _out558;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out559;
                  (this).GenExpr(_2119_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out557, out _out558, out _out559);
                  _2120_lExpr = _out557;
                  _2121___v199 = _out558;
                  _2122_recIdentsL = _out559;
                  _2118_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2118_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2120_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2122_recIdentsL);
                }
              }
            }
            if (unmatched103) {
              unmatched103 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source104 = _2113_high;
            bool unmatched104 = true;
            if (unmatched104) {
              if (_source104.is_Some) {
                DAST._IExpression _2123_h = _source104.dtor_value;
                unmatched104 = false;
                {
                  RAST._IExpr _2124_hExpr;
                  DCOMP._IOwnership _2125___v200;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2126_recIdentsH;
                  RAST._IExpr _out560;
                  DCOMP._IOwnership _out561;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out562;
                  (this).GenExpr(_2123_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out560, out _out561, out _out562);
                  _2124_hExpr = _out560;
                  _2125___v200 = _out561;
                  _2126_recIdentsH = _out562;
                  _2118_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2118_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2124_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2126_recIdentsH);
                }
              }
            }
            if (unmatched104) {
              unmatched104 = false;
            }
            r = _2114_onExpr;
            if (_2111_isArray) {
              if (!(_2117_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2117_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2117_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).FSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2117_methodName))).Apply(_2118_arguments);
            } else {
              if (!(_2117_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2117_methodName)).Apply(_2118_arguments);
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
      if (unmatched100) {
        if (_source100.is_TupleSelect) {
          DAST._IExpression _2127_on = _source100.dtor_expr;
          BigInteger _2128_idx = _source100.dtor_index;
          DAST._IType _2129_fieldType = _source100.dtor_fieldType;
          unmatched100 = false;
          {
            RAST._IExpr _2130_onExpr;
            DCOMP._IOwnership _2131_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2132_recIdents;
            RAST._IExpr _out565;
            DCOMP._IOwnership _out566;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out567;
            (this).GenExpr(_2127_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out565, out _out566, out _out567);
            _2130_onExpr = _out565;
            _2131_onOwnership = _out566;
            _2132_recIdents = _out567;
            Dafny.ISequence<Dafny.Rune> _2133_selName;
            _2133_selName = Std.Strings.__default.OfNat(_2128_idx);
            DAST._IType _source105 = _2129_fieldType;
            bool unmatched105 = true;
            if (unmatched105) {
              if (_source105.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2134_tps = _source105.dtor_Tuple_a0;
                unmatched105 = false;
                if (((_2129_fieldType).is_Tuple) && ((new BigInteger((_2134_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2133_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2133_selName);
                }
              }
            }
            if (unmatched105) {
              unmatched105 = false;
            }
            r = ((_2130_onExpr).Sel(_2133_selName)).Clone();
            RAST._IExpr _out568;
            DCOMP._IOwnership _out569;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out568, out _out569);
            r = _out568;
            resultingOwnership = _out569;
            readIdents = _2132_recIdents;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_Call) {
          DAST._IExpression _2135_on = _source100.dtor_on;
          DAST._ICallName _2136_name = _source100.dtor_callName;
          Dafny.ISequence<DAST._IType> _2137_typeArgs = _source100.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2138_args = _source100.dtor_args;
          unmatched100 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2139_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2140_recIdents;
            Dafny.ISequence<RAST._IType> _2141_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2142_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out570;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out571;
            Dafny.ISequence<RAST._IType> _out572;
            Std.Wrappers._IOption<DAST._IResolvedType> _out573;
            (this).GenArgs(selfIdent, _2136_name, _2137_typeArgs, _2138_args, env, out _out570, out _out571, out _out572, out _out573);
            _2139_argExprs = _out570;
            _2140_recIdents = _out571;
            _2141_typeExprs = _out572;
            _2142_fullNameQualifier = _out573;
            readIdents = _2140_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source106 = _2142_fullNameQualifier;
            bool unmatched106 = true;
            if (unmatched106) {
              if (_source106.is_Some) {
                DAST._IResolvedType value11 = _source106.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2143_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2144_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2145_base = value11.dtor_kind;
                unmatched106 = false;
                RAST._IExpr _2146_fullPath;
                RAST._IExpr _out574;
                _out574 = DCOMP.COMP.GenPathExpr(_2143_path, true);
                _2146_fullPath = _out574;
                Dafny.ISequence<RAST._IType> _2147_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out575;
                _out575 = (this).GenTypeArgs(_2144_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2147_onTypeExprs = _out575;
                RAST._IExpr _2148_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2149_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2150_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2145_base).is_Trait) || ((_2145_base).is_Class)) {
                  RAST._IExpr _out576;
                  DCOMP._IOwnership _out577;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out578;
                  (this).GenExpr(_2135_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out576, out _out577, out _out578);
                  _2148_onExpr = _out576;
                  _2149_recOwnership = _out577;
                  _2150_recIdents = _out578;
                  _2148_onExpr = ((this).read__macro).Apply1(_2148_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2150_recIdents);
                } else {
                  RAST._IExpr _out579;
                  DCOMP._IOwnership _out580;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out581;
                  (this).GenExpr(_2135_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out579, out _out580, out _out581);
                  _2148_onExpr = _out579;
                  _2149_recOwnership = _out580;
                  _2150_recIdents = _out581;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2150_recIdents);
                }
                r = ((((_2146_fullPath).ApplyType(_2147_onTypeExprs)).FSel(DCOMP.__default.escapeName((_2136_name).dtor_name))).ApplyType(_2141_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2148_onExpr), _2139_argExprs));
                RAST._IExpr _out582;
                DCOMP._IOwnership _out583;
                (this).FromOwned(r, expectedOwnership, out _out582, out _out583);
                r = _out582;
                resultingOwnership = _out583;
              }
            }
            if (unmatched106) {
              unmatched106 = false;
              RAST._IExpr _2151_onExpr;
              DCOMP._IOwnership _2152___v206;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2153_recIdents;
              RAST._IExpr _out584;
              DCOMP._IOwnership _out585;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
              (this).GenExpr(_2135_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out584, out _out585, out _out586);
              _2151_onExpr = _out584;
              _2152___v206 = _out585;
              _2153_recIdents = _out586;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2153_recIdents);
              Dafny.ISequence<Dafny.Rune> _2154_renderedName;
              _2154_renderedName = (this).GetMethodName(_2135_on, _2136_name);
              DAST._IExpression _source107 = _2135_on;
              bool unmatched107 = true;
              if (unmatched107) {
                bool disjunctiveMatch16 = false;
                if (_source107.is_Companion) {
                  disjunctiveMatch16 = true;
                }
                if (_source107.is_ExternCompanion) {
                  disjunctiveMatch16 = true;
                }
                if (disjunctiveMatch16) {
                  unmatched107 = false;
                  {
                    _2151_onExpr = (_2151_onExpr).FSel(_2154_renderedName);
                  }
                }
              }
              if (unmatched107) {
                unmatched107 = false;
                {
                  if (!object.Equals(_2151_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source108 = _2136_name;
                    bool unmatched108 = true;
                    if (unmatched108) {
                      if (_source108.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source108.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2155_tpe = onType2.dtor_value;
                          unmatched108 = false;
                          RAST._IType _2156_typ;
                          RAST._IType _out587;
                          _out587 = (this).GenType(_2155_tpe, DCOMP.GenTypeContext.@default());
                          _2156_typ = _out587;
                          if ((_2156_typ).IsObjectOrPointer()) {
                            _2151_onExpr = ((this).read__macro).Apply1(_2151_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched108) {
                      unmatched108 = false;
                    }
                  }
                  _2151_onExpr = (_2151_onExpr).Sel(_2154_renderedName);
                }
              }
              r = ((_2151_onExpr).ApplyType(_2141_typeExprs)).Apply(_2139_argExprs);
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
      if (unmatched100) {
        if (_source100.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2157_paramsDafny = _source100.dtor_params;
          DAST._IType _2158_retType = _source100.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2159_body = _source100.dtor_body;
          unmatched100 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2160_params;
            Dafny.ISequence<RAST._IFormal> _out590;
            _out590 = (this).GenParams(_2157_paramsDafny, true);
            _2160_params = _out590;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2161_paramNames;
            _2161_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2162_paramTypesMap;
            _2162_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi49 = new BigInteger((_2160_params).Count);
            for (BigInteger _2163_i = BigInteger.Zero; _2163_i < _hi49; _2163_i++) {
              Dafny.ISequence<Dafny.Rune> _2164_name;
              _2164_name = ((_2160_params).Select(_2163_i)).dtor_name;
              _2161_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2161_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2164_name));
              _2162_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2162_paramTypesMap, _2164_name, ((_2160_params).Select(_2163_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2165_subEnv;
            _2165_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2161_paramNames, _2162_paramTypesMap));
            RAST._IExpr _2166_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2167_recIdents;
            DCOMP._IEnvironment _2168___v216;
            RAST._IExpr _out591;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out592;
            DCOMP._IEnvironment _out593;
            (this).GenStmts(_2159_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2165_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out591, out _out592, out _out593);
            _2166_recursiveGen = _out591;
            _2167_recIdents = _out592;
            _2168___v216 = _out593;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2167_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2167_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2169_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll7 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_7 in (_2169_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2170_name = (Dafny.ISequence<Dafny.Rune>)_compr_7;
                if ((_2169_paramNames).Contains(_2170_name)) {
                  _coll7.Add(_2170_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll7);
            }))())(_2161_paramNames));
            RAST._IExpr _2171_allReadCloned;
            _2171_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2167_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2172_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2167_recIdents).Elements) {
                _2172_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_2167_recIdents).Contains(_2172_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 5142)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2172_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2173_selfCloned;
                DCOMP._IOwnership _2174___v217;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2175___v218;
                RAST._IExpr _out594;
                DCOMP._IOwnership _out595;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out596;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out594, out _out595, out _out596);
                _2173_selfCloned = _out594;
                _2174___v217 = _out595;
                _2175___v218 = _out596;
                _2171_allReadCloned = (_2171_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2173_selfCloned)));
              } else if (!((_2161_paramNames).Contains(_2172_next))) {
                RAST._IExpr _2176_copy;
                _2176_copy = (RAST.Expr.create_Identifier(_2172_next)).Clone();
                _2171_allReadCloned = (_2171_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2172_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2176_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2172_next));
              }
              _2167_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2167_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2172_next));
            }
            RAST._IType _2177_retTypeGen;
            RAST._IType _out597;
            _out597 = (this).GenType(_2158_retType, DCOMP.GenTypeContext.InFn());
            _2177_retTypeGen = _out597;
            r = RAST.Expr.create_Block((_2171_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2160_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2177_retTypeGen), RAST.Expr.create_Block(_2166_recursiveGen)))));
            RAST._IExpr _out598;
            DCOMP._IOwnership _out599;
            (this).FromOwned(r, expectedOwnership, out _out598, out _out599);
            r = _out598;
            resultingOwnership = _out599;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2178_values = _source100.dtor_values;
          DAST._IType _2179_retType = _source100.dtor_retType;
          DAST._IExpression _2180_expr = _source100.dtor_expr;
          unmatched100 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2181_paramNames;
            _2181_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2182_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out600;
            _out600 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2183_value) => {
              return (_2183_value).dtor__0;
            })), _2178_values), false);
            _2182_paramFormals = _out600;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2184_paramTypes;
            _2184_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2185_paramNamesSet;
            _2185_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi50 = new BigInteger((_2178_values).Count);
            for (BigInteger _2186_i = BigInteger.Zero; _2186_i < _hi50; _2186_i++) {
              Dafny.ISequence<Dafny.Rune> _2187_name;
              _2187_name = (((_2178_values).Select(_2186_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2188_rName;
              _2188_rName = DCOMP.__default.escapeVar(_2187_name);
              _2181_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2181_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2188_rName));
              _2184_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2184_paramTypes, _2188_rName, ((_2182_paramFormals).Select(_2186_i)).dtor_tpe);
              _2185_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2185_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2188_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi51 = new BigInteger((_2178_values).Count);
            for (BigInteger _2189_i = BigInteger.Zero; _2189_i < _hi51; _2189_i++) {
              RAST._IType _2190_typeGen;
              RAST._IType _out601;
              _out601 = (this).GenType((((_2178_values).Select(_2189_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2190_typeGen = _out601;
              RAST._IExpr _2191_valueGen;
              DCOMP._IOwnership _2192___v219;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2193_recIdents;
              RAST._IExpr _out602;
              DCOMP._IOwnership _out603;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out604;
              (this).GenExpr(((_2178_values).Select(_2189_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out602, out _out603, out _out604);
              _2191_valueGen = _out602;
              _2192___v219 = _out603;
              _2193_recIdents = _out604;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar((((_2178_values).Select(_2189_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2190_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2191_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2193_recIdents);
            }
            DCOMP._IEnvironment _2194_newEnv;
            _2194_newEnv = DCOMP.Environment.create(_2181_paramNames, _2184_paramTypes);
            RAST._IExpr _2195_recGen;
            DCOMP._IOwnership _2196_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2197_recIdents;
            RAST._IExpr _out605;
            DCOMP._IOwnership _out606;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out607;
            (this).GenExpr(_2180_expr, selfIdent, _2194_newEnv, expectedOwnership, out _out605, out _out606, out _out607);
            _2195_recGen = _out605;
            _2196_recOwned = _out606;
            _2197_recIdents = _out607;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2197_recIdents, _2185_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2195_recGen));
            RAST._IExpr _out608;
            DCOMP._IOwnership _out609;
            (this).FromOwnership(r, _2196_recOwned, expectedOwnership, out _out608, out _out609);
            r = _out608;
            resultingOwnership = _out609;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2198_name = _source100.dtor_ident;
          DAST._IType _2199_tpe = _source100.dtor_typ;
          DAST._IExpression _2200_value = _source100.dtor_value;
          DAST._IExpression _2201_iifeBody = _source100.dtor_iifeBody;
          unmatched100 = false;
          {
            RAST._IExpr _2202_valueGen;
            DCOMP._IOwnership _2203___v220;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2204_recIdents;
            RAST._IExpr _out610;
            DCOMP._IOwnership _out611;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out612;
            (this).GenExpr(_2200_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out610, out _out611, out _out612);
            _2202_valueGen = _out610;
            _2203___v220 = _out611;
            _2204_recIdents = _out612;
            readIdents = _2204_recIdents;
            RAST._IType _2205_valueTypeGen;
            RAST._IType _out613;
            _out613 = (this).GenType(_2199_tpe, DCOMP.GenTypeContext.InFn());
            _2205_valueTypeGen = _out613;
            RAST._IExpr _2206_bodyGen;
            DCOMP._IOwnership _2207___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2208_bodyIdents;
            RAST._IExpr _out614;
            DCOMP._IOwnership _out615;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out616;
            (this).GenExpr(_2201_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out614, out _out615, out _out616);
            _2206_bodyGen = _out614;
            _2207___v221 = _out615;
            _2208_bodyIdents = _out616;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2208_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_2198_name))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar(_2198_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2205_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2202_valueGen))).Then(_2206_bodyGen));
            RAST._IExpr _out617;
            DCOMP._IOwnership _out618;
            (this).FromOwned(r, expectedOwnership, out _out617, out _out618);
            r = _out617;
            resultingOwnership = _out618;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_Apply) {
          DAST._IExpression _2209_func = _source100.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2210_args = _source100.dtor_args;
          unmatched100 = false;
          {
            RAST._IExpr _2211_funcExpr;
            DCOMP._IOwnership _2212___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2213_recIdents;
            RAST._IExpr _out619;
            DCOMP._IOwnership _out620;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out621;
            (this).GenExpr(_2209_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out619, out _out620, out _out621);
            _2211_funcExpr = _out619;
            _2212___v222 = _out620;
            _2213_recIdents = _out621;
            readIdents = _2213_recIdents;
            Dafny.ISequence<RAST._IExpr> _2214_rArgs;
            _2214_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi52 = new BigInteger((_2210_args).Count);
            for (BigInteger _2215_i = BigInteger.Zero; _2215_i < _hi52; _2215_i++) {
              RAST._IExpr _2216_argExpr;
              DCOMP._IOwnership _2217_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2218_argIdents;
              RAST._IExpr _out622;
              DCOMP._IOwnership _out623;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out624;
              (this).GenExpr((_2210_args).Select(_2215_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out622, out _out623, out _out624);
              _2216_argExpr = _out622;
              _2217_argOwned = _out623;
              _2218_argIdents = _out624;
              _2214_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2214_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2216_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2218_argIdents);
            }
            r = (_2211_funcExpr).Apply(_2214_rArgs);
            RAST._IExpr _out625;
            DCOMP._IOwnership _out626;
            (this).FromOwned(r, expectedOwnership, out _out625, out _out626);
            r = _out625;
            resultingOwnership = _out626;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_TypeTest) {
          DAST._IExpression _2219_on = _source100.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2220_dType = _source100.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2221_variant = _source100.dtor_variant;
          unmatched100 = false;
          {
            RAST._IExpr _2222_exprGen;
            DCOMP._IOwnership _2223___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2224_recIdents;
            RAST._IExpr _out627;
            DCOMP._IOwnership _out628;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out629;
            (this).GenExpr(_2219_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out627, out _out628, out _out629);
            _2222_exprGen = _out627;
            _2223___v223 = _out628;
            _2224_recIdents = _out629;
            RAST._IType _2225_dTypePath;
            RAST._IType _out630;
            _out630 = DCOMP.COMP.GenPathType(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2220_dType, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2221_variant)));
            _2225_dTypePath = _out630;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2222_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_2225_dTypePath)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out631;
            DCOMP._IOwnership _out632;
            (this).FromOwned(r, expectedOwnership, out _out631, out _out632);
            r = _out631;
            resultingOwnership = _out632;
            readIdents = _2224_recIdents;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_Is) {
          DAST._IExpression _2226_expr = _source100.dtor_expr;
          DAST._IType _2227_fromType = _source100.dtor_fromType;
          DAST._IType _2228_toType = _source100.dtor_toType;
          unmatched100 = false;
          {
            RAST._IExpr _2229_expr;
            DCOMP._IOwnership _2230_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2231_recIdents;
            RAST._IExpr _out633;
            DCOMP._IOwnership _out634;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out635;
            (this).GenExpr(_2226_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out633, out _out634, out _out635);
            _2229_expr = _out633;
            _2230_recOwned = _out634;
            _2231_recIdents = _out635;
            RAST._IType _2232_fromType;
            RAST._IType _out636;
            _out636 = (this).GenType(_2227_fromType, DCOMP.GenTypeContext.@default());
            _2232_fromType = _out636;
            RAST._IType _2233_toType;
            RAST._IType _out637;
            _out637 = (this).GenType(_2228_toType, DCOMP.GenTypeContext.@default());
            _2233_toType = _out637;
            if (((_2232_fromType).IsObject()) && ((_2233_toType).IsObject())) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is_instance_of_object"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((_2232_fromType).ObjectOrPointerUnderlying(), (_2233_toType).ObjectOrPointerUnderlying()))).Apply1(_2229_expr);
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Source and/or target types of type test is/are not Object"));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
            RAST._IExpr _out638;
            DCOMP._IOwnership _out639;
            (this).FromOwnership(r, _2230_recOwned, expectedOwnership, out _out638, out _out639);
            r = _out638;
            resultingOwnership = _out639;
            readIdents = _2231_recIdents;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_BoolBoundedPool) {
          unmatched100 = false;
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
      if (unmatched100) {
        if (_source100.is_SetBoundedPool) {
          DAST._IExpression _2234_of = _source100.dtor_of;
          unmatched100 = false;
          {
            RAST._IExpr _2235_exprGen;
            DCOMP._IOwnership _2236___v224;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2237_recIdents;
            RAST._IExpr _out642;
            DCOMP._IOwnership _out643;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out644;
            (this).GenExpr(_2234_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out642, out _out643, out _out644);
            _2235_exprGen = _out642;
            _2236___v224 = _out643;
            _2237_recIdents = _out644;
            r = ((_2235_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out645;
            DCOMP._IOwnership _out646;
            (this).FromOwned(r, expectedOwnership, out _out645, out _out646);
            r = _out645;
            resultingOwnership = _out646;
            readIdents = _2237_recIdents;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_SeqBoundedPool) {
          DAST._IExpression _2238_of = _source100.dtor_of;
          bool _2239_includeDuplicates = _source100.dtor_includeDuplicates;
          unmatched100 = false;
          {
            RAST._IExpr _2240_exprGen;
            DCOMP._IOwnership _2241___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2242_recIdents;
            RAST._IExpr _out647;
            DCOMP._IOwnership _out648;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out649;
            (this).GenExpr(_2238_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out647, out _out648, out _out649);
            _2240_exprGen = _out647;
            _2241___v225 = _out648;
            _2242_recIdents = _out649;
            r = ((_2240_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2239_includeDuplicates)) {
              r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).AsExpr()).Apply1(r);
            }
            RAST._IExpr _out650;
            DCOMP._IOwnership _out651;
            (this).FromOwned(r, expectedOwnership, out _out650, out _out651);
            r = _out650;
            resultingOwnership = _out651;
            readIdents = _2242_recIdents;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MapBoundedPool) {
          DAST._IExpression _2243_of = _source100.dtor_of;
          unmatched100 = false;
          {
            RAST._IExpr _2244_exprGen;
            DCOMP._IOwnership _2245___v226;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2246_recIdents;
            RAST._IExpr _out652;
            DCOMP._IOwnership _out653;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out654;
            (this).GenExpr(_2243_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out652, out _out653, out _out654);
            _2244_exprGen = _out652;
            _2245___v226 = _out653;
            _2246_recIdents = _out654;
            r = ((((_2244_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2246_recIdents;
            RAST._IExpr _out655;
            DCOMP._IOwnership _out656;
            (this).FromOwned(r, expectedOwnership, out _out655, out _out656);
            r = _out655;
            resultingOwnership = _out656;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_IntRange) {
          DAST._IExpression _2247_lo = _source100.dtor_lo;
          DAST._IExpression _2248_hi = _source100.dtor_hi;
          bool _2249_up = _source100.dtor_up;
          unmatched100 = false;
          {
            RAST._IExpr _2250_lo;
            DCOMP._IOwnership _2251___v227;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2252_recIdentsLo;
            RAST._IExpr _out657;
            DCOMP._IOwnership _out658;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out659;
            (this).GenExpr(_2247_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out657, out _out658, out _out659);
            _2250_lo = _out657;
            _2251___v227 = _out658;
            _2252_recIdentsLo = _out659;
            RAST._IExpr _2253_hi;
            DCOMP._IOwnership _2254___v228;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2255_recIdentsHi;
            RAST._IExpr _out660;
            DCOMP._IOwnership _out661;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out662;
            (this).GenExpr(_2248_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out660, out _out661, out _out662);
            _2253_hi = _out660;
            _2254___v228 = _out661;
            _2255_recIdentsHi = _out662;
            if (_2249_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2250_lo, _2253_hi));
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).AsExpr()).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2253_hi, _2250_lo));
            }
            RAST._IExpr _out663;
            DCOMP._IOwnership _out664;
            (this).FromOwned(r, expectedOwnership, out _out663, out _out664);
            r = _out663;
            resultingOwnership = _out664;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2252_recIdentsLo, _2255_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_UnboundedIntRange) {
          DAST._IExpression _2256_start = _source100.dtor_start;
          bool _2257_up = _source100.dtor_up;
          unmatched100 = false;
          {
            RAST._IExpr _2258_start;
            DCOMP._IOwnership _2259___v229;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2260_recIdentStart;
            RAST._IExpr _out665;
            DCOMP._IOwnership _out666;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out667;
            (this).GenExpr(_2256_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out665, out _out666, out _out667);
            _2258_start = _out665;
            _2259___v229 = _out666;
            _2260_recIdentStart = _out667;
            if (_2257_up) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).AsExpr()).Apply1(_2258_start);
            } else {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).AsExpr()).Apply1(_2258_start);
            }
            RAST._IExpr _out668;
            DCOMP._IOwnership _out669;
            (this).FromOwned(r, expectedOwnership, out _out668, out _out669);
            r = _out668;
            resultingOwnership = _out669;
            readIdents = _2260_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched100) {
        if (_source100.is_MapBuilder) {
          DAST._IType _2261_keyType = _source100.dtor_keyType;
          DAST._IType _2262_valueType = _source100.dtor_valueType;
          unmatched100 = false;
          {
            RAST._IType _2263_kType;
            RAST._IType _out670;
            _out670 = (this).GenType(_2261_keyType, DCOMP.GenTypeContext.@default());
            _2263_kType = _out670;
            RAST._IType _2264_vType;
            RAST._IType _out671;
            _out671 = (this).GenType(_2262_valueType, DCOMP.GenTypeContext.@default());
            _2264_vType = _out671;
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2263_kType, _2264_vType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
      if (unmatched100) {
        if (_source100.is_SetBuilder) {
          DAST._IType _2265_elemType = _source100.dtor_elemType;
          unmatched100 = false;
          {
            RAST._IType _2266_eType;
            RAST._IType _out674;
            _out674 = (this).GenType(_2265_elemType, DCOMP.GenTypeContext.@default());
            _2266_eType = _out674;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = (((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).AsExpr()).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2266_eType))).FSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out675;
            DCOMP._IOwnership _out676;
            (this).FromOwned(r, expectedOwnership, out _out675, out _out676);
            r = _out675;
            resultingOwnership = _out676;
            return ;
          }
        }
      }
      if (unmatched100) {
        DAST._IType _2267_elemType = _source100.dtor_elemType;
        DAST._IExpression _2268_collection = _source100.dtor_collection;
        bool _2269_is__forall = _source100.dtor_is__forall;
        DAST._IExpression _2270_lambda = _source100.dtor_lambda;
        unmatched100 = false;
        {
          RAST._IType _2271_tpe;
          RAST._IType _out677;
          _out677 = (this).GenType(_2267_elemType, DCOMP.GenTypeContext.@default());
          _2271_tpe = _out677;
          RAST._IExpr _2272_collectionGen;
          DCOMP._IOwnership _2273___v230;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2274_recIdents;
          RAST._IExpr _out678;
          DCOMP._IOwnership _out679;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out680;
          (this).GenExpr(_2268_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out678, out _out679, out _out680);
          _2272_collectionGen = _out678;
          _2273___v230 = _out679;
          _2274_recIdents = _out680;
          Dafny.ISequence<DAST._IAttribute> _2275_extraAttributes;
          _2275_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2268_collection).is_IntRange) || ((_2268_collection).is_UnboundedIntRange)) || ((_2268_collection).is_SeqBoundedPool)) {
            _2275_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2270_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2276_formals;
            _2276_formals = (_2270_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2277_newFormals;
            _2277_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi53 = new BigInteger((_2276_formals).Count);
            for (BigInteger _2278_i = BigInteger.Zero; _2278_i < _hi53; _2278_i++) {
              var _pat_let_tv145 = _2275_extraAttributes;
              var _pat_let_tv146 = _2276_formals;
              _2277_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2277_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2276_formals).Select(_2278_i), _pat_let38_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let38_0, _2279_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv145, ((_pat_let_tv146).Select(_2278_i)).dtor_attributes), _pat_let39_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let39_0, _2280_dt__update_hattributes_h0 => DAST.Formal.create((_2279_dt__update__tmp_h0).dtor_name, (_2279_dt__update__tmp_h0).dtor_typ, _2280_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv147 = _2277_newFormals;
            DAST._IExpression _2281_newLambda;
            _2281_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2270_lambda, _pat_let40_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let40_0, _2282_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv147, _pat_let41_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let41_0, _2283_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2283_dt__update_hparams_h0, (_2282_dt__update__tmp_h1).dtor_retType, (_2282_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2284_lambdaGen;
            DCOMP._IOwnership _2285___v231;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2286_recLambdaIdents;
            RAST._IExpr _out681;
            DCOMP._IOwnership _out682;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out683;
            (this).GenExpr(_2281_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out681, out _out682, out _out683);
            _2284_lambdaGen = _out681;
            _2285___v231 = _out682;
            _2286_recLambdaIdents = _out683;
            Dafny.ISequence<Dafny.Rune> _2287_fn;
            _2287_fn = ((_2269_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2272_collectionGen).Sel(_2287_fn)).Apply1(((_2284_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2274_recIdents, _2286_recLambdaIdents);
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
      Dafny.ISequence<RAST._IModDecl> _2288_externUseDecls;
      _2288_externUseDecls = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi54 = new BigInteger((externalFiles).Count);
      for (BigInteger _2289_i = BigInteger.Zero; _2289_i < _hi54; _2289_i++) {
        Dafny.ISequence<Dafny.Rune> _2290_externalFile;
        _2290_externalFile = (externalFiles).Select(_2289_i);
        Dafny.ISequence<Dafny.Rune> _2291_externalMod;
        _2291_externalMod = _2290_externalFile;
        if (((new BigInteger((_2290_externalFile).Count)) > (new BigInteger(3))) && (((_2290_externalFile).Drop((new BigInteger((_2290_externalFile).Count)) - (new BigInteger(3)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".rs")))) {
          _2291_externalMod = (_2290_externalFile).Subsequence(BigInteger.Zero, (new BigInteger((_2290_externalFile).Count)) - (new BigInteger(3)));
        } else {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unrecognized external file "), _2290_externalFile), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". External file must be *.rs files")));
        }
        RAST._IMod _2292_externMod;
        _2292_externMod = RAST.Mod.create_ExternMod(_2291_externalMod);
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (_2292_externMod)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        _2288_externUseDecls = Dafny.Sequence<RAST._IModDecl>.Concat(_2288_externUseDecls, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), ((RAST.__default.crate).MSel(_2291_externalMod)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))));
      }
      if (!(_2288_externUseDecls).Equals(Dafny.Sequence<RAST._IModDecl>.FromElements())) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (RAST.Mod.create_Mod(DCOMP.COMP.DAFNY__EXTERN__MODULE, _2288_externUseDecls))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
      }
      BigInteger _hi55 = new BigInteger((p).Count);
      for (BigInteger _2293_i = BigInteger.Zero; _2293_i < _hi55; _2293_i++) {
        RAST._IMod _2294_m;
        RAST._IMod _out686;
        _out686 = (this).GenModule((p).Select(_2293_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2294_m = _out686;
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (_2294_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2295_i;
      _2295_i = BigInteger.Zero;
      while ((_2295_i) < (new BigInteger((fullName).Count))) {
        if ((_2295_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2295_i)));
        _2295_i = (_2295_i) + (BigInteger.One);
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