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
      if ((DCOMP.__default.reserved__vars).Contains(_1140_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _1140_r);
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
      var _pat_let_tv139 = dafnyName;
      var _pat_let_tv140 = rs;
      var _pat_let_tv141 = dafnyName;
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _1141_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source52 = (rs).Select(BigInteger.Zero);
          bool unmatched52 = true;
          if (unmatched52) {
            if (_source52.is_UserDefined) {
              DAST._IResolvedType _1142_resolvedType = _source52.dtor_resolved;
              unmatched52 = false;
              return DCOMP.__default.TraitTypeContainingMethod(_1142_resolvedType, _pat_let_tv139);
            }
          }
          if (unmatched52) {
            unmatched52 = false;
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
          throw new System.Exception("unexpected control point");
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source53 = _1141_res;
        bool unmatched53 = true;
        if (unmatched53) {
          if (_source53.is_Some) {
            unmatched53 = false;
            return _1141_res;
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
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1143_path = _let_tmp_rhs53.dtor_path;
      Dafny.ISequence<DAST._IType> _1144_typeArgs = _let_tmp_rhs53.dtor_typeArgs;
      DAST._IResolvedTypeBase _1145_kind = _let_tmp_rhs53.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1146_attributes = _let_tmp_rhs53.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1147_properMethods = _let_tmp_rhs53.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1148_extendedTypes = _let_tmp_rhs53.dtor_extendedTypes;
      if ((_1147_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1148_extendedTypes, dafnyName);
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
      Dafny.ISequence<Dafny.Rune> _1149___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1149___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((s).Select(BigInteger.Zero)) == (new Dafny.Rune(' '))) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1149___accumulator, s);
      } else {
        _1149___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1149___accumulator, ((((s).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")) : (Dafny.Sequence<Dafny.Rune>.FromElements((s).Select(BigInteger.Zero)))));
        Dafny.ISequence<Dafny.Rune> _in128 = (s).Drop(BigInteger.One);
        s = _in128;
        goto TAIL_CALL_START;
      }
    }
    public static DCOMP._IExternAttribute ExtractExtern(Dafny.ISequence<DAST._IAttribute> attributes, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DCOMP._IExternAttribute res = DCOMP.ExternAttribute.Default();
      BigInteger _hi5 = new BigInteger((attributes).Count);
      for (BigInteger _1150_i = BigInteger.Zero; _1150_i < _hi5; _1150_i++) {
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _1151_attr;
        _1151_attr = DCOMP.__default.OptExtern((attributes).Select(_1150_i), dafnyName);
        Std.Wrappers._IOption<DCOMP._IExternAttribute> _source54 = _1151_attr;
        bool unmatched54 = true;
        if (unmatched54) {
          if (_source54.is_Some) {
            DCOMP._IExternAttribute _1152_n = _source54.dtor_value;
            unmatched54 = false;
            res = _1152_n;
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
      DCOMP._IEnvironment _1153_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1154_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll6 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1155_k = (Dafny.ISequence<Dafny.Rune>)_compr_6;
          if (((this).dtor_types).Contains(_1155_k)) {
            _coll6.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_1155_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_1155_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll6);
      }))();
      return DCOMP.Environment.create((_1153_dt__update__tmp_h0).dtor_names, _1154_dt__update_htypes_h0);
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
      BigInteger _1156_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1156_indexInEnv), ((this).dtor_names).Drop((_1156_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _1157_modName;
      _1157_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1157_modName);
      } else {
        DCOMP._IExternAttribute _1158_optExtern;
        _1158_optExtern = DCOMP.__default.ExtractExternMod(mod);
        Dafny.ISequence<RAST._IModDecl> _1159_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1159_body = _out15;
        if ((_1158_optExtern).is_SimpleExtern) {
          if ((mod).dtor_requiresExterns) {
            _1159_body = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"))).MSel(DCOMP.COMP.DAFNY__EXTERN__MODULE)).MSel(DCOMP.__default.ReplaceDotByDoubleColon((_1158_optExtern).dtor_overrideName))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))), _1159_body);
          }
        } else if ((_1158_optExtern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Externs on modules can only have 1 string argument"));
        } else if ((_1158_optExtern).is_UnsupportedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some((_1158_optExtern).dtor_reason);
        }
        s = RAST.Mod.create_Mod(_1157_modName, _1159_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi6 = new BigInteger((body).Count);
      for (BigInteger _1160_i = BigInteger.Zero; _1160_i < _hi6; _1160_i++) {
        Dafny.ISequence<RAST._IModDecl> _1161_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source55 = (body).Select(_1160_i);
        bool unmatched55 = true;
        if (unmatched55) {
          if (_source55.is_Module) {
            DAST._IModule _1162_m = _source55.dtor_Module_a0;
            unmatched55 = false;
            RAST._IMod _1163_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1162_m, containingPath);
            _1163_mm = _out16;
            _1161_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1163_mm));
          }
        }
        if (unmatched55) {
          if (_source55.is_Class) {
            DAST._IClass _1164_c = _source55.dtor_Class_a0;
            unmatched55 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1164_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1164_c).dtor_name)));
            _1161_generated = _out17;
          }
        }
        if (unmatched55) {
          if (_source55.is_Trait) {
            DAST._ITrait _1165_t = _source55.dtor_Trait_a0;
            unmatched55 = false;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenTrait(_1165_t, containingPath);
            _1161_generated = _out18;
          }
        }
        if (unmatched55) {
          if (_source55.is_Newtype) {
            DAST._INewtype _1166_n = _source55.dtor_Newtype_a0;
            unmatched55 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1166_n);
            _1161_generated = _out19;
          }
        }
        if (unmatched55) {
          if (_source55.is_SynonymType) {
            DAST._ISynonymType _1167_s = _source55.dtor_SynonymType_a0;
            unmatched55 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1167_s);
            _1161_generated = _out20;
          }
        }
        if (unmatched55) {
          DAST._IDatatype _1168_d = _source55.dtor_Datatype_a0;
          unmatched55 = false;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1168_d);
          _1161_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1161_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1169_genTpConstraint;
      _1169_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1169_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1169_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1169_genTpConstraint);
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
        for (BigInteger _1170_tpI = BigInteger.Zero; _1170_tpI < _hi7; _1170_tpI++) {
          DAST._ITypeArgDecl _1171_tp;
          _1171_tp = (@params).Select(_1170_tpI);
          DAST._IType _1172_typeArg;
          RAST._ITypeParamDecl _1173_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1171_tp, out _out22, out _out23);
          _1172_typeArg = _out22;
          _1173_typeParam = _out23;
          RAST._IType _1174_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1172_typeArg, DCOMP.GenTypeContext.@default());
          _1174_rType = _out24;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1172_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1174_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1173_typeParam));
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
      Dafny.ISequence<DAST._IType> _1175_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1176_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1177_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1178_whereConstraints;
      Dafny.ISequence<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1175_typeParamsSeq = _out25;
      _1176_rTypeParams = _out26;
      _1177_rTypeParamsDecls = _out27;
      _1178_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1179_constrainedTypeParams;
      _1179_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1177_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1180_fields;
      _1180_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1181_fieldInits;
      _1181_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi8 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1182_fieldI = BigInteger.Zero; _1182_fieldI < _hi8; _1182_fieldI++) {
        DAST._IField _1183_field;
        _1183_field = ((c).dtor_fields).Select(_1182_fieldI);
        RAST._IType _1184_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1183_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1184_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1185_fieldRustName;
        _1185_fieldRustName = DCOMP.__default.escapeVar(((_1183_field).dtor_formal).dtor_name);
        _1180_fields = Dafny.Sequence<RAST._IField>.Concat(_1180_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1185_fieldRustName, _1184_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source56 = (_1183_field).dtor_defaultValue;
        bool unmatched56 = true;
        if (unmatched56) {
          if (_source56.is_Some) {
            DAST._IExpression _1186_e = _source56.dtor_value;
            unmatched56 = false;
            {
              RAST._IExpr _1187_expr;
              DCOMP._IOwnership _1188___v49;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1189___v50;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1186_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1187_expr = _out30;
              _1188___v49 = _out31;
              _1189___v50 = _out32;
              _1181_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1181_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1185_fieldRustName, _1187_expr)));
            }
          }
        }
        if (unmatched56) {
          unmatched56 = false;
          {
            RAST._IExpr _1190_default;
            _1190_default = RAST.__default.std__Default__default;
            if ((_1184_fieldType).IsObjectOrPointer()) {
              _1190_default = (_1184_fieldType).ToNullExpr();
            }
            _1181_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1181_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1185_fieldRustName, _1190_default)));
          }
        }
      }
      BigInteger _hi9 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1191_typeParamI = BigInteger.Zero; _1191_typeParamI < _hi9; _1191_typeParamI++) {
        DAST._IType _1192_typeArg;
        RAST._ITypeParamDecl _1193_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1191_typeParamI), out _out33, out _out34);
        _1192_typeArg = _out33;
        _1193_typeParam = _out34;
        RAST._IType _1194_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1192_typeArg, DCOMP.GenTypeContext.@default());
        _1194_rTypeArg = _out35;
        _1180_fields = Dafny.Sequence<RAST._IField>.Concat(_1180_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1191_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1194_rTypeArg))))));
        _1181_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1181_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1191_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      DCOMP._IExternAttribute _1195_extern;
      _1195_extern = DCOMP.__default.ExtractExtern((c).dtor_attributes, (c).dtor_name);
      Dafny.ISequence<Dafny.Rune> _1196_className = Dafny.Sequence<Dafny.Rune>.Empty;
      if ((_1195_extern).is_SimpleExtern) {
        _1196_className = (_1195_extern).dtor_overrideName;
      } else {
        _1196_className = DCOMP.__default.escapeName((c).dtor_name);
        if ((_1195_extern).is_AdvancedExtern) {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multi-argument externs not supported for classes yet"));
        }
      }
      RAST._IStruct _1197_struct;
      _1197_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1196_className, _1177_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1180_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((_1195_extern).is_NoExtern) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1197_struct)));
      }
      Dafny.ISequence<RAST._IImplMember> _1198_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1199_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1175_typeParamsSeq, out _out36, out _out37);
      _1198_implBody = _out36;
      _1199_traitBodies = _out37;
      if (((_1195_extern).is_NoExtern) && (!(_1196_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default")))) {
        _1198_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.Type.create_SelfOwned())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel((this).allocate)).ApplyType1(RAST.Type.create_SelfOwned())).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1198_implBody);
      }
      RAST._IType _1200_selfTypeForImpl = RAST.Type.Default();
      if (((_1195_extern).is_NoExtern) || ((_1195_extern).is_UnsupportedExtern)) {
        _1200_selfTypeForImpl = RAST.Type.create_TIdentifier(_1196_className);
      } else if ((_1195_extern).is_AdvancedExtern) {
        _1200_selfTypeForImpl = ((RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"))).MSel((_1195_extern).dtor_enclosingModule)).MSel((_1195_extern).dtor_overrideName);
      } else if ((_1195_extern).is_SimpleExtern) {
        _1200_selfTypeForImpl = RAST.Type.create_TIdentifier((_1195_extern).dtor_overrideName);
      }
      if ((new BigInteger((_1198_implBody).Count)).Sign == 1) {
        RAST._IImpl _1201_i;
        _1201_i = RAST.Impl.create_Impl(_1177_rTypeParamsDecls, RAST.Type.create_TypeApp(_1200_selfTypeForImpl, _1176_rTypeParams), _1178_whereConstraints, _1198_implBody);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1201_i)));
      }
      RAST._IType _1202_genSelfPath;
      RAST._IType _out38;
      _out38 = DCOMP.COMP.GenPath(path);
      _1202_genSelfPath = _out38;
      if (!(_1196_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1177_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"))))), RAST.Type.create_TypeApp(_1202_genSelfPath, _1176_rTypeParams), _1178_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any")))))))))));
      }
      Dafny.ISequence<DAST._IType> _1203_superClasses;
      _1203_superClasses = (((_1196_className).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_default"))) ? (Dafny.Sequence<DAST._IType>.FromElements()) : ((c).dtor_superClasses));
      BigInteger _hi10 = new BigInteger((_1203_superClasses).Count);
      for (BigInteger _1204_i = BigInteger.Zero; _1204_i < _hi10; _1204_i++) {
        DAST._IType _1205_superClass;
        _1205_superClass = (_1203_superClasses).Select(_1204_i);
        DAST._IType _source57 = _1205_superClass;
        bool unmatched57 = true;
        if (unmatched57) {
          if (_source57.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source57.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1206_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1207_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1208_properMethods = resolved0.dtor_properMethods;
              unmatched57 = false;
              {
                RAST._IType _1209_pathStr;
                RAST._IType _out39;
                _out39 = DCOMP.COMP.GenPath(_1206_traitPath);
                _1209_pathStr = _out39;
                Dafny.ISequence<RAST._IType> _1210_typeArgs;
                Dafny.ISequence<RAST._IType> _out40;
                _out40 = (this).GenTypeArgs(_1207_typeArgs, DCOMP.GenTypeContext.@default());
                _1210_typeArgs = _out40;
                Dafny.ISequence<RAST._IImplMember> _1211_body;
                _1211_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1199_traitBodies).Contains(_1206_traitPath)) {
                  _1211_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1199_traitBodies,_1206_traitPath);
                }
                RAST._IType _1212_traitType;
                _1212_traitType = RAST.Type.create_TypeApp(_1209_pathStr, _1210_typeArgs);
                if (!((_1195_extern).is_NoExtern)) {
                  if (((new BigInteger((_1211_body).Count)).Sign == 0) && ((new BigInteger((_1208_properMethods).Count)).Sign != 0)) {
                    goto continue_0;
                  }
                  if ((new BigInteger((_1211_body).Count)) != (new BigInteger((_1208_properMethods).Count))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: In the class "), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(path, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1213_s) => {
  return ((_1213_s));
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", some proper methods of ")), (_1212_traitType)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" are marked {:extern} and some are not.")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" For the Rust compiler, please make all methods (")), RAST.__default.SeqToString<Dafny.ISequence<Dafny.Rune>>(_1208_properMethods, ((System.Func<Dafny.ISequence<Dafny.Rune>, Dafny.ISequence<Dafny.Rune>>)((_1214_s) => {
  return (_1214_s);
})), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")  bodiless and mark as {:extern} and implement them in a Rust file, ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("or mark none of them as {:extern} and implement them in Dafny. ")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.")));
                  }
                }
                RAST._IModDecl _1215_x;
                _1215_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1177_rTypeParamsDecls, _1212_traitType, RAST.Type.create_TypeApp(_1202_genSelfPath, _1176_rTypeParams), _1178_whereConstraints, _1211_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1215_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1177_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1212_traitType))), RAST.Type.create_TypeApp(_1202_genSelfPath, _1176_rTypeParams), _1178_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1212_traitType)))))))));
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
      Dafny.ISequence<DAST._IType> _1216_typeParamsSeq;
      _1216_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1217_typeParamDecls;
      _1217_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1218_typeParams;
      _1218_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi11 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1219_tpI = BigInteger.Zero; _1219_tpI < _hi11; _1219_tpI++) {
          DAST._ITypeArgDecl _1220_tp;
          _1220_tp = ((t).dtor_typeParams).Select(_1219_tpI);
          DAST._IType _1221_typeArg;
          RAST._ITypeParamDecl _1222_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1220_tp, out _out41, out _out42);
          _1221_typeArg = _out41;
          _1222_typeParamDecl = _out42;
          _1216_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1216_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1221_typeArg));
          _1217_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1217_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1222_typeParamDecl));
          RAST._IType _1223_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1221_typeArg, DCOMP.GenTypeContext.@default());
          _1223_typeParam = _out43;
          _1218_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1218_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1223_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1224_fullPath;
      _1224_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1225_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1226___v54;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1224_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1216_typeParamsSeq, out _out44, out _out45);
      _1225_implBody = _out44;
      _1226___v54 = _out45;
      Dafny.ISequence<RAST._IType> _1227_parents;
      _1227_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi12 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1228_i = BigInteger.Zero; _1228_i < _hi12; _1228_i++) {
        RAST._IType _1229_tpe;
        RAST._IType _out46;
        _out46 = (this).GenType(((t).dtor_parents).Select(_1228_i), DCOMP.GenTypeContext.ForTraitParents());
        _1229_tpe = _out46;
        _1227_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1227_parents, Dafny.Sequence<RAST._IType>.FromElements(_1229_tpe)), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply1(RAST.Type.create_DynType(_1229_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1217_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1218_typeParams), _1227_parents, _1225_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1230_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1231_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1232_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1233_whereConstraints;
      Dafny.ISequence<DAST._IType> _out47;
      Dafny.ISequence<RAST._IType> _out48;
      Dafny.ISequence<RAST._ITypeParamDecl> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1230_typeParamsSeq = _out47;
      _1231_rTypeParams = _out48;
      _1232_rTypeParamsDecls = _out49;
      _1233_whereConstraints = _out50;
      Dafny.ISequence<Dafny.Rune> _1234_constrainedTypeParams;
      _1234_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1232_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1235_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source58 = DCOMP.COMP.NewtypeRangeToRustType((c).dtor_range);
      bool unmatched58 = true;
      if (unmatched58) {
        if (_source58.is_Some) {
          RAST._IType _1236_v = _source58.dtor_value;
          unmatched58 = false;
          _1235_underlyingType = _1236_v;
        }
      }
      if (unmatched58) {
        unmatched58 = false;
        RAST._IType _out51;
        _out51 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1235_underlyingType = _out51;
      }
      DAST._IType _1237_resultingType;
      _1237_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1238_newtypeName;
      _1238_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1238_newtypeName, _1232_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1235_underlyingType))))));
      RAST._IExpr _1239_fnBody;
      _1239_fnBody = RAST.Expr.create_Identifier(_1238_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source59 = (c).dtor_witnessExpr;
      bool unmatched59 = true;
      if (unmatched59) {
        if (_source59.is_Some) {
          DAST._IExpression _1240_e = _source59.dtor_value;
          unmatched59 = false;
          {
            DAST._IExpression _1241_e;
            _1241_e = ((object.Equals((c).dtor_base, _1237_resultingType)) ? (_1240_e) : (DAST.Expression.create_Convert(_1240_e, (c).dtor_base, _1237_resultingType)));
            RAST._IExpr _1242_eStr;
            DCOMP._IOwnership _1243___v55;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1244___v56;
            RAST._IExpr _out52;
            DCOMP._IOwnership _out53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out54;
            (this).GenExpr(_1241_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out52, out _out53, out _out54);
            _1242_eStr = _out52;
            _1243___v55 = _out53;
            _1244___v56 = _out54;
            _1239_fnBody = (_1239_fnBody).Apply1(_1242_eStr);
          }
        }
      }
      if (unmatched59) {
        unmatched59 = false;
        {
          _1239_fnBody = (_1239_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1245_body;
      _1245_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1239_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source60 = (c).dtor_constraint;
      bool unmatched60 = true;
      if (unmatched60) {
        if (_source60.is_None) {
          unmatched60 = false;
        }
      }
      if (unmatched60) {
        DAST._INewtypeConstraint value8 = _source60.dtor_value;
        DAST._IFormal _1246_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1247_constraintStmts = value8.dtor_constraintStmts;
        unmatched60 = false;
        RAST._IExpr _1248_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1249___v57;
        DCOMP._IEnvironment _1250_newEnv;
        RAST._IExpr _out55;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out56;
        DCOMP._IEnvironment _out57;
        (this).GenStmts(_1247_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out55, out _out56, out _out57);
        _1248_rStmts = _out55;
        _1249___v57 = _out56;
        _1250_newEnv = _out57;
        Dafny.ISequence<RAST._IFormal> _1251_rFormals;
        Dafny.ISequence<RAST._IFormal> _out58;
        _out58 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1246_formal), false);
        _1251_rFormals = _out58;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1232_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1238_newtypeName), _1231_rTypeParams), _1233_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1251_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1248_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1232_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1238_newtypeName), _1231_rTypeParams), _1233_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1245_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1232_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1238_newtypeName), _1231_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1232_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1238_newtypeName), _1231_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1235_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1252_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1253_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1254_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1255_whereConstraints;
      Dafny.ISequence<DAST._IType> _out59;
      Dafny.ISequence<RAST._IType> _out60;
      Dafny.ISequence<RAST._ITypeParamDecl> _out61;
      Dafny.ISequence<Dafny.Rune> _out62;
      (this).GenTypeParameters((c).dtor_typeParams, out _out59, out _out60, out _out61, out _out62);
      _1252_typeParamsSeq = _out59;
      _1253_rTypeParams = _out60;
      _1254_rTypeParamsDecls = _out61;
      _1255_whereConstraints = _out62;
      Dafny.ISequence<Dafny.Rune> _1256_synonymTypeName;
      _1256_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1257_resultingType;
      RAST._IType _out63;
      _out63 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1257_resultingType = _out63;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1256_synonymTypeName, _1254_rTypeParamsDecls, _1257_resultingType)));
      Dafny.ISequence<RAST._ITypeParamDecl> _1258_defaultConstrainedTypeParams;
      _1258_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1254_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Std.Wrappers._IOption<DAST._IExpression> _source61 = (c).dtor_witnessExpr;
      bool unmatched61 = true;
      if (unmatched61) {
        if (_source61.is_Some) {
          DAST._IExpression _1259_e = _source61.dtor_value;
          unmatched61 = false;
          {
            RAST._IExpr _1260_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1261___v58;
            DCOMP._IEnvironment _1262_newEnv;
            RAST._IExpr _out64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out65;
            DCOMP._IEnvironment _out66;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out64, out _out65, out _out66);
            _1260_rStmts = _out64;
            _1261___v58 = _out65;
            _1262_newEnv = _out66;
            RAST._IExpr _1263_rExpr;
            DCOMP._IOwnership _1264___v59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1265___v60;
            RAST._IExpr _out67;
            DCOMP._IOwnership _out68;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out69;
            (this).GenExpr(_1259_e, DCOMP.SelfInfo.create_NoSelf(), _1262_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out67, out _out68, out _out69);
            _1263_rExpr = _out67;
            _1264___v59 = _out68;
            _1265___v60 = _out69;
            Dafny.ISequence<Dafny.Rune> _1266_constantName;
            _1266_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1266_constantName, _1258_defaultConstrainedTypeParams, Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1257_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1260_rStmts).Then(_1263_rExpr)))))));
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
          Dafny.ISequence<DAST._IType> _1267_ts = _source62.dtor_Tuple_a0;
          unmatched62 = false;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1268_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1268_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1269_t = (DAST._IType)_forall_var_5;
            return !((_1268_ts).Contains(_1269_t)) || ((this).TypeIsEq(_1269_t));
          }))))(_1267_ts);
        }
      }
      if (unmatched62) {
        if (_source62.is_Array) {
          DAST._IType _1270_t = _source62.dtor_element;
          unmatched62 = false;
          return (this).TypeIsEq(_1270_t);
        }
      }
      if (unmatched62) {
        if (_source62.is_Seq) {
          DAST._IType _1271_t = _source62.dtor_element;
          unmatched62 = false;
          return (this).TypeIsEq(_1271_t);
        }
      }
      if (unmatched62) {
        if (_source62.is_Set) {
          DAST._IType _1272_t = _source62.dtor_element;
          unmatched62 = false;
          return (this).TypeIsEq(_1272_t);
        }
      }
      if (unmatched62) {
        if (_source62.is_Multiset) {
          DAST._IType _1273_t = _source62.dtor_element;
          unmatched62 = false;
          return (this).TypeIsEq(_1273_t);
        }
      }
      if (unmatched62) {
        if (_source62.is_Map) {
          DAST._IType _1274_k = _source62.dtor_key;
          DAST._IType _1275_v = _source62.dtor_value;
          unmatched62 = false;
          return ((this).TypeIsEq(_1274_k)) && ((this).TypeIsEq(_1275_v));
        }
      }
      if (unmatched62) {
        if (_source62.is_SetBuilder) {
          DAST._IType _1276_t = _source62.dtor_element;
          unmatched62 = false;
          return (this).TypeIsEq(_1276_t);
        }
      }
      if (unmatched62) {
        if (_source62.is_MapBuilder) {
          DAST._IType _1277_k = _source62.dtor_key;
          DAST._IType _1278_v = _source62.dtor_value;
          unmatched62 = false;
          return ((this).TypeIsEq(_1277_k)) && ((this).TypeIsEq(_1278_v));
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
          Dafny.ISequence<Dafny.Rune> _1279_i = _source62.dtor_TypeArg_a0;
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
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1280_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1280_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1281_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1281_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1282_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1280_c).dtor_ctors).Contains(_1281_ctor)) && (((_1281_ctor).dtor_args).Contains(_1282_arg))) || ((this).TypeIsEq(((_1282_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1283_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1284_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1285_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1286_whereConstraints;
      Dafny.ISequence<DAST._IType> _out70;
      Dafny.ISequence<RAST._IType> _out71;
      Dafny.ISequence<RAST._ITypeParamDecl> _out72;
      Dafny.ISequence<Dafny.Rune> _out73;
      (this).GenTypeParameters((c).dtor_typeParams, out _out70, out _out71, out _out72, out _out73);
      _1283_typeParamsSeq = _out70;
      _1284_rTypeParams = _out71;
      _1285_rTypeParamsDecls = _out72;
      _1286_whereConstraints = _out73;
      Dafny.ISequence<Dafny.Rune> _1287_datatypeName;
      _1287_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1288_ctors;
      _1288_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _1289_variances;
      _1289_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_1290_typeParamDecl) => {
        return (_1290_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      BigInteger _hi13 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1291_i = BigInteger.Zero; _1291_i < _hi13; _1291_i++) {
        DAST._IDatatypeCtor _1292_ctor;
        _1292_ctor = ((c).dtor_ctors).Select(_1291_i);
        Dafny.ISequence<RAST._IField> _1293_ctorArgs;
        _1293_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1294_isNumeric;
        _1294_isNumeric = false;
        BigInteger _hi14 = new BigInteger(((_1292_ctor).dtor_args).Count);
        for (BigInteger _1295_j = BigInteger.Zero; _1295_j < _hi14; _1295_j++) {
          DAST._IDatatypeDtor _1296_dtor;
          _1296_dtor = ((_1292_ctor).dtor_args).Select(_1295_j);
          RAST._IType _1297_formalType;
          RAST._IType _out74;
          _out74 = (this).GenType(((_1296_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1297_formalType = _out74;
          Dafny.ISequence<Dafny.Rune> _1298_formalName;
          _1298_formalName = DCOMP.__default.escapeVar(((_1296_dtor).dtor_formal).dtor_name);
          if (((_1295_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1298_formalName))) {
            _1294_isNumeric = true;
          }
          if ((((_1295_j).Sign != 0) && (_1294_isNumeric)) && (!(Std.Strings.__default.OfNat(_1295_j)).Equals(_1298_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1298_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1295_j)));
            _1294_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1293_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1293_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1298_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1297_formalType))))));
          } else {
            _1293_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1293_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1298_formalName, _1297_formalType))));
          }
        }
        RAST._IFields _1299_namedFields;
        _1299_namedFields = RAST.Fields.create_NamedFields(_1293_ctorArgs);
        if (_1294_isNumeric) {
          _1299_namedFields = (_1299_namedFields).ToNamelessFields();
        }
        _1288_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1288_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1292_ctor).dtor_name), _1299_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1300_selfPath;
      _1300_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1301_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1302_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out75;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out76;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1300_selfPath, _1283_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1289_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1283_typeParamsSeq, out _out75, out _out76);
      _1301_implBodyRaw = _out75;
      _1302_traitBodies = _out76;
      Dafny.ISequence<RAST._IImplMember> _1303_implBody;
      _1303_implBody = _1301_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1304_emittedFields;
      _1304_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi15 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1305_i = BigInteger.Zero; _1305_i < _hi15; _1305_i++) {
        DAST._IDatatypeCtor _1306_ctor;
        _1306_ctor = ((c).dtor_ctors).Select(_1305_i);
        BigInteger _hi16 = new BigInteger(((_1306_ctor).dtor_args).Count);
        for (BigInteger _1307_j = BigInteger.Zero; _1307_j < _hi16; _1307_j++) {
          DAST._IDatatypeDtor _1308_dtor;
          _1308_dtor = ((_1306_ctor).dtor_args).Select(_1307_j);
          Dafny.ISequence<Dafny.Rune> _1309_callName;
          _1309_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1308_dtor).dtor_callName, DCOMP.__default.escapeVar(((_1308_dtor).dtor_formal).dtor_name));
          if (!((_1304_emittedFields).Contains(_1309_callName))) {
            _1304_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1304_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1309_callName));
            RAST._IType _1310_formalType;
            RAST._IType _out77;
            _out77 = (this).GenType(((_1308_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1310_formalType = _out77;
            Dafny.ISequence<RAST._IMatchCase> _1311_cases;
            _1311_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi17 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1312_k = BigInteger.Zero; _1312_k < _hi17; _1312_k++) {
              DAST._IDatatypeCtor _1313_ctor2;
              _1313_ctor2 = ((c).dtor_ctors).Select(_1312_k);
              Dafny.ISequence<Dafny.Rune> _1314_pattern;
              _1314_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1287_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1313_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1315_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1316_hasMatchingField;
              _1316_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1317_patternInner;
              _1317_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1318_isNumeric;
              _1318_isNumeric = false;
              BigInteger _hi18 = new BigInteger(((_1313_ctor2).dtor_args).Count);
              for (BigInteger _1319_l = BigInteger.Zero; _1319_l < _hi18; _1319_l++) {
                DAST._IDatatypeDtor _1320_dtor2;
                _1320_dtor2 = ((_1313_ctor2).dtor_args).Select(_1319_l);
                Dafny.ISequence<Dafny.Rune> _1321_patternName;
                _1321_patternName = DCOMP.__default.escapeVar(((_1320_dtor2).dtor_formal).dtor_name);
                if (((_1319_l).Sign == 0) && ((_1321_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1318_isNumeric = true;
                }
                if (_1318_isNumeric) {
                  _1321_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1320_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1319_l)));
                }
                if (object.Equals(((_1308_dtor).dtor_formal).dtor_name, ((_1320_dtor2).dtor_formal).dtor_name)) {
                  _1316_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1321_patternName);
                }
                _1317_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1317_patternInner, _1321_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1318_isNumeric) {
                _1314_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1314_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1317_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1314_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1314_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1317_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1316_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1315_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1316_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1315_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1316_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1315_rhs = (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("field does not exist on this variant"));
              }
              RAST._IMatchCase _1322_ctorMatch;
              _1322_ctorMatch = RAST.MatchCase.create(_1314_pattern, RAST.Expr.create_RawExpr(_1315_rhs));
              _1311_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1311_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1322_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1311_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1311_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1287_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr((this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))))));
            }
            RAST._IExpr _1323_methodBody;
            _1323_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1311_cases);
            _1303_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1303_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1309_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1310_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1323_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1324_coerceTypes;
      _1324_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1325_rCoerceTypeParams;
      _1325_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1326_coerceArguments;
      _1326_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1327_coerceMap;
      _1327_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1328_rCoerceMap;
      _1328_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1329_coerceMapToArg;
      _1329_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1330_types;
        _1330_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi19 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1331_typeI = BigInteger.Zero; _1331_typeI < _hi19; _1331_typeI++) {
          DAST._ITypeArgDecl _1332_typeParam;
          _1332_typeParam = ((c).dtor_typeParams).Select(_1331_typeI);
          DAST._IType _1333_typeArg;
          RAST._ITypeParamDecl _1334_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(_1332_typeParam, out _out78, out _out79);
          _1333_typeArg = _out78;
          _1334_rTypeParamDecl = _out79;
          RAST._IType _1335_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1333_typeArg, DCOMP.GenTypeContext.@default());
          _1335_rTypeArg = _out80;
          _1330_types = Dafny.Sequence<RAST._IType>.Concat(_1330_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1335_rTypeArg))));
          if (((_1331_typeI) < (new BigInteger((_1289_variances).Count))) && (((_1289_variances).Select(_1331_typeI)).is_Nonvariant)) {
            _1324_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1324_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1335_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1336_coerceTypeParam;
          _1336_coerceTypeParam = Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_1332_typeParam, _pat_let9_0 => Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_pat_let9_0, _1337_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1331_typeI)), _pat_let10_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(_pat_let10_0, _1338_dt__update_hname_h0 => DAST.TypeArgDecl.create(_1338_dt__update_hname_h0, (_1337_dt__update__tmp_h0).dtor_bounds, (_1337_dt__update__tmp_h0).dtor_variance)))));
          DAST._IType _1339_coerceTypeArg;
          RAST._ITypeParamDecl _1340_rCoerceTypeParamDecl;
          DAST._IType _out81;
          RAST._ITypeParamDecl _out82;
          (this).GenTypeParam(_1336_coerceTypeParam, out _out81, out _out82);
          _1339_coerceTypeArg = _out81;
          _1340_rCoerceTypeParamDecl = _out82;
          _1327_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1327_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1333_typeArg, _1339_coerceTypeArg)));
          RAST._IType _1341_rCoerceType;
          RAST._IType _out83;
          _out83 = (this).GenType(_1339_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1341_rCoerceType = _out83;
          _1328_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1328_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1335_rTypeArg, _1341_rCoerceType)));
          _1324_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1324_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1341_rCoerceType));
          _1325_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1325_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1340_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1342_coerceFormal;
          _1342_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1331_typeI));
          _1329_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1329_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1335_rTypeArg, _1341_rCoerceType), (RAST.Expr.create_Identifier(_1342_coerceFormal)).Clone())));
          _1326_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1326_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1342_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1335_rTypeArg), _1341_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        _1288_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1288_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1343_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1343_tpe);
})), _1330_types)))));
      }
      bool _1344_cIsEq;
      _1344_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1344_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1287_datatypeName, _1285_rTypeParamsDecls, _1288_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1285_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1287_datatypeName), _1284_rTypeParams), _1286_whereConstraints, _1303_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1345_printImplBodyCases;
      _1345_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1346_hashImplBodyCases;
      _1346_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1347_coerceImplBodyCases;
      _1347_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi20 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1348_i = BigInteger.Zero; _1348_i < _hi20; _1348_i++) {
        DAST._IDatatypeCtor _1349_ctor;
        _1349_ctor = ((c).dtor_ctors).Select(_1348_i);
        Dafny.ISequence<Dafny.Rune> _1350_ctorMatch;
        _1350_ctorMatch = DCOMP.__default.escapeName((_1349_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1351_modulePrefix;
        _1351_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1352_ctorName;
        _1352_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1351_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1349_ctor).dtor_name));
        if (((new BigInteger((_1352_ctorName).Count)) >= (new BigInteger(13))) && (((_1352_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1352_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1353_printRhs;
        _1353_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1352_ctorName), (((_1349_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1354_hashRhs;
        _1354_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1355_coerceRhsArgs;
        _1355_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1356_isNumeric;
        _1356_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1357_ctorMatchInner;
        _1357_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi21 = new BigInteger(((_1349_ctor).dtor_args).Count);
        for (BigInteger _1358_j = BigInteger.Zero; _1358_j < _hi21; _1358_j++) {
          DAST._IDatatypeDtor _1359_dtor;
          _1359_dtor = ((_1349_ctor).dtor_args).Select(_1358_j);
          Dafny.ISequence<Dafny.Rune> _1360_patternName;
          _1360_patternName = DCOMP.__default.escapeVar(((_1359_dtor).dtor_formal).dtor_name);
          DAST._IType _1361_formalType;
          _1361_formalType = ((_1359_dtor).dtor_formal).dtor_typ;
          if (((_1358_j).Sign == 0) && ((_1360_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1356_isNumeric = true;
          }
          if (_1356_isNumeric) {
            _1360_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1359_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1358_j)));
          }
          _1354_hashRhs = (((_1361_formalType).is_Arrow) ? ((_1354_hashRhs).Then(((RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))))) : ((_1354_hashRhs).Then(((((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1360_patternName), RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state")))))));
          _1357_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1357_ctorMatchInner, _1360_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1358_j).Sign == 1) {
            _1353_printRhs = (_1353_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1353_printRhs = (_1353_printRhs).Then(RAST.Expr.create_RawExpr((((_1361_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1360_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1362_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1363_formalTpe;
          RAST._IType _out84;
          _out84 = (this).GenType(_1361_formalType, DCOMP.GenTypeContext.@default());
          _1363_formalTpe = _out84;
          DAST._IType _1364_newFormalType;
          _1364_newFormalType = (_1361_formalType).Replace(_1327_coerceMap);
          RAST._IType _1365_newFormalTpe;
          _1365_newFormalTpe = (_1363_formalTpe).Replace(_1328_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1366_upcastConverter;
          _1366_upcastConverter = (this).UpcastConversionLambda(_1361_formalType, _1363_formalTpe, _1364_newFormalType, _1365_newFormalTpe, _1329_coerceMapToArg);
          if ((_1366_upcastConverter).is_Success) {
            RAST._IExpr _1367_coercionFunction;
            _1367_coercionFunction = (_1366_upcastConverter).dtor_value;
            _1362_coerceRhsArg = (_1367_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1360_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1358_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1287_datatypeName));
            _1362_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1355_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1355_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1360_patternName, _1362_coerceRhsArg)));
        }
        RAST._IExpr _1368_coerceRhs;
        _1368_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1287_datatypeName)).MSel(DCOMP.__default.escapeName((_1349_ctor).dtor_name)), _1355_coerceRhsArgs);
        if (_1356_isNumeric) {
          _1350_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1350_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1357_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1350_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1350_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1357_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1349_ctor).dtor_hasAnyArgs) {
          _1353_printRhs = (_1353_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1353_printRhs = (_1353_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1345_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1345_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1287_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1350_ctorMatch), RAST.Expr.create_Block(_1353_printRhs))));
        _1346_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1346_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1287_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1350_ctorMatch), RAST.Expr.create_Block(_1354_hashRhs))));
        _1347_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1347_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1287_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1350_ctorMatch), RAST.Expr.create_Block(_1368_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1369_extraCases;
        _1369_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1287_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{"), (this).UnreachablePanicIfVerified(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}")))));
        _1345_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1345_printImplBodyCases, _1369_extraCases);
        _1346_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1346_hashImplBodyCases, _1369_extraCases);
        _1347_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1347_coerceImplBodyCases, _1369_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1370_defaultConstrainedTypeParams;
      _1370_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1285_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1371_rTypeParamsDeclsWithEq;
      _1371_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1285_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1372_rTypeParamsDeclsWithHash;
      _1372_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1285_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1373_printImplBody;
      _1373_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1345_printImplBodyCases);
      RAST._IExpr _1374_hashImplBody;
      _1374_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1346_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1285_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1287_datatypeName), _1284_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1285_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1287_datatypeName), _1284_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1373_printImplBody))))))));
      if ((new BigInteger((_1325_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1375_coerceImplBody;
        _1375_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1347_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1285_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1287_datatypeName), _1284_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1325_rCoerceTypeParams, _1326_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1287_datatypeName), _1284_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1287_datatypeName), _1324_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.Type.create_SelfOwned())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1287_datatypeName), _1324_coerceTypes)), _1375_coerceImplBody))))))))));
      }
      if (_1344_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1371_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1287_datatypeName), _1284_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1372_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1287_datatypeName), _1284_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1374_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1376_structName;
        _1376_structName = (RAST.Expr.create_Identifier(_1287_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1377_structAssignments;
        _1377_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi22 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1378_i = BigInteger.Zero; _1378_i < _hi22; _1378_i++) {
          DAST._IDatatypeDtor _1379_dtor;
          _1379_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1378_i);
          _1377_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1377_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(((_1379_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1380_defaultConstrainedTypeParams;
        _1380_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1285_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1381_fullType;
        _1381_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1287_datatypeName), _1284_rTypeParams);
        if (_1344_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1380_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1381_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1381_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1376_structName, _1377_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1285_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1381_fullType), RAST.Type.create_Borrowed(_1381_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        for (BigInteger _1382_i = BigInteger.Zero; _1382_i < _hi23; _1382_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1382_i))));
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
        for (BigInteger _1383_i = BigInteger.Zero; _1383_i < _hi24; _1383_i++) {
          Dafny.ISequence<Dafny.Rune> _1384_id;
          _1384_id = ((p).Select(_1383_i));
          r = (r).MSel(((escape) ? (DCOMP.__default.escapeName(_1384_id)) : (DCOMP.__default.ReplaceDotByDoubleColon((_1384_id)))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi25 = new BigInteger((args).Count);
      for (BigInteger _1385_i = BigInteger.Zero; _1385_i < _hi25; _1385_i++) {
        RAST._IType _1386_genTp;
        RAST._IType _out85;
        _out85 = (this).GenType((args).Select(_1385_i), genTypeContext);
        _1386_genTp = _out85;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1386_genTp));
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
          DAST._IResolvedType _1387_resolved = _source63.dtor_resolved;
          unmatched63 = false;
          {
            RAST._IType _1388_t;
            RAST._IType _out86;
            _out86 = DCOMP.COMP.GenPath((_1387_resolved).dtor_path);
            _1388_t = _out86;
            Dafny.ISequence<RAST._IType> _1389_typeArgs;
            Dafny.ISequence<RAST._IType> _out87;
            _out87 = (this).GenTypeArgs((_1387_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _1390_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _1391_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1390_dt__update__tmp_h0).dtor_inBinding, (_1390_dt__update__tmp_h0).dtor_inFn, _1391_dt__update_hforTraitParents_h0))))));
            _1389_typeArgs = _out87;
            s = RAST.Type.create_TypeApp(_1388_t, _1389_typeArgs);
            DAST._IResolvedTypeBase _source64 = (_1387_resolved).dtor_kind;
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
                  if ((this).IsRcWrapped((_1387_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched64) {
              if (_source64.is_Trait) {
                unmatched64 = false;
                {
                  if (((_1387_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched64) {
              DAST._IType _1392_base = _source64.dtor_baseType;
              DAST._INewtypeRange _1393_range = _source64.dtor_range;
              bool _1394_erased = _source64.dtor_erase;
              unmatched64 = false;
              {
                if (_1394_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source65 = DCOMP.COMP.NewtypeRangeToRustType(_1393_range);
                  bool unmatched65 = true;
                  if (unmatched65) {
                    if (_source65.is_Some) {
                      RAST._IType _1395_v = _source65.dtor_value;
                      unmatched65 = false;
                      s = _1395_v;
                    }
                  }
                  if (unmatched65) {
                    unmatched65 = false;
                    RAST._IType _1396_underlying;
                    RAST._IType _out88;
                    _out88 = (this).GenType(_1392_base, DCOMP.GenTypeContext.@default());
                    _1396_underlying = _out88;
                    s = RAST.Type.create_TSynonym(s, _1396_underlying);
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
          Dafny.ISequence<DAST._IType> _1397_types = _source63.dtor_Tuple_a0;
          unmatched63 = false;
          {
            Dafny.ISequence<RAST._IType> _1398_args;
            _1398_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1399_i;
            _1399_i = BigInteger.Zero;
            while ((_1399_i) < (new BigInteger((_1397_types).Count))) {
              RAST._IType _1400_generated;
              RAST._IType _out89;
              _out89 = (this).GenType((_1397_types).Select(_1399_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _1401_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _1402_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1401_dt__update__tmp_h1).dtor_inBinding, (_1401_dt__update__tmp_h1).dtor_inFn, _1402_dt__update_hforTraitParents_h1))))));
              _1400_generated = _out89;
              _1398_args = Dafny.Sequence<RAST._IType>.Concat(_1398_args, Dafny.Sequence<RAST._IType>.FromElements(_1400_generated));
              _1399_i = (_1399_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1397_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1398_args)) : (RAST.__default.SystemTupleType(_1398_args)));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Array) {
          DAST._IType _1403_element = _source63.dtor_element;
          BigInteger _1404_dims = _source63.dtor_dims;
          unmatched63 = false;
          {
            if ((_1404_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1405_elem;
              RAST._IType _out90;
              _out90 = (this).GenType(_1403_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _1406_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _1407_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1406_dt__update__tmp_h2).dtor_inBinding, (_1406_dt__update__tmp_h2).dtor_inFn, _1407_dt__update_hforTraitParents_h2))))));
              _1405_elem = _out90;
              if ((_1404_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1405_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1408_n;
                _1408_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1404_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1408_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1405_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Seq) {
          DAST._IType _1409_element = _source63.dtor_element;
          unmatched63 = false;
          {
            RAST._IType _1410_elem;
            RAST._IType _out91;
            _out91 = (this).GenType(_1409_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _1411_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _1412_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1411_dt__update__tmp_h3).dtor_inBinding, (_1411_dt__update__tmp_h3).dtor_inFn, _1412_dt__update_hforTraitParents_h3))))));
            _1410_elem = _out91;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1410_elem));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Set) {
          DAST._IType _1413_element = _source63.dtor_element;
          unmatched63 = false;
          {
            RAST._IType _1414_elem;
            RAST._IType _out92;
            _out92 = (this).GenType(_1413_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _1415_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _1416_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1415_dt__update__tmp_h4).dtor_inBinding, (_1415_dt__update__tmp_h4).dtor_inFn, _1416_dt__update_hforTraitParents_h4))))));
            _1414_elem = _out92;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1414_elem));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Multiset) {
          DAST._IType _1417_element = _source63.dtor_element;
          unmatched63 = false;
          {
            RAST._IType _1418_elem;
            RAST._IType _out93;
            _out93 = (this).GenType(_1417_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _1419_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _1420_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1419_dt__update__tmp_h5).dtor_inBinding, (_1419_dt__update__tmp_h5).dtor_inFn, _1420_dt__update_hforTraitParents_h5))))));
            _1418_elem = _out93;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1418_elem));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Map) {
          DAST._IType _1421_key = _source63.dtor_key;
          DAST._IType _1422_value = _source63.dtor_value;
          unmatched63 = false;
          {
            RAST._IType _1423_keyType;
            RAST._IType _out94;
            _out94 = (this).GenType(_1421_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _1424_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _1425_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1424_dt__update__tmp_h6).dtor_inBinding, (_1424_dt__update__tmp_h6).dtor_inFn, _1425_dt__update_hforTraitParents_h6))))));
            _1423_keyType = _out94;
            RAST._IType _1426_valueType;
            RAST._IType _out95;
            _out95 = (this).GenType(_1422_value, genTypeContext);
            _1426_valueType = _out95;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1423_keyType, _1426_valueType));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_MapBuilder) {
          DAST._IType _1427_key = _source63.dtor_key;
          DAST._IType _1428_value = _source63.dtor_value;
          unmatched63 = false;
          {
            RAST._IType _1429_keyType;
            RAST._IType _out96;
            _out96 = (this).GenType(_1427_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _1430_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _1431_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1430_dt__update__tmp_h7).dtor_inBinding, (_1430_dt__update__tmp_h7).dtor_inFn, _1431_dt__update_hforTraitParents_h7))))));
            _1429_keyType = _out96;
            RAST._IType _1432_valueType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1428_value, genTypeContext);
            _1432_valueType = _out97;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1429_keyType, _1432_valueType));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_SetBuilder) {
          DAST._IType _1433_elem = _source63.dtor_element;
          unmatched63 = false;
          {
            RAST._IType _1434_elemType;
            RAST._IType _out98;
            _out98 = (this).GenType(_1433_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _1435_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _1436_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1435_dt__update__tmp_h8).dtor_inBinding, (_1435_dt__update__tmp_h8).dtor_inFn, _1436_dt__update_hforTraitParents_h8))))));
            _1434_elemType = _out98;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1434_elemType));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1437_args = _source63.dtor_args;
          DAST._IType _1438_result = _source63.dtor_result;
          unmatched63 = false;
          {
            Dafny.ISequence<RAST._IType> _1439_argTypes;
            _1439_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1440_i;
            _1440_i = BigInteger.Zero;
            while ((_1440_i) < (new BigInteger((_1437_args).Count))) {
              RAST._IType _1441_generated;
              RAST._IType _out99;
              _out99 = (this).GenType((_1437_args).Select(_1440_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let29_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let29_0, _1442_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let30_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let30_0, _1443_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let31_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let31_0, _1444_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1442_dt__update__tmp_h9).dtor_inBinding, _1444_dt__update_hinFn_h0, _1443_dt__update_hforTraitParents_h9))))))));
              _1441_generated = _out99;
              _1439_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1439_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1441_generated)));
              _1440_i = (_1440_i) + (BigInteger.One);
            }
            RAST._IType _1445_resultType;
            RAST._IType _out100;
            _out100 = (this).GenType(_1438_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1445_resultType = _out100;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1439_argTypes, _1445_resultType)));
          }
        }
      }
      if (unmatched63) {
        if (_source63.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source63.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1446_name = _h90;
          unmatched63 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1446_name));
        }
      }
      if (unmatched63) {
        if (_source63.is_Primitive) {
          DAST._IPrimitive _1447_p = _source63.dtor_Primitive_a0;
          unmatched63 = false;
          {
            DAST._IPrimitive _source66 = _1447_p;
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
        Dafny.ISequence<Dafny.Rune> _1448_v = _source63.dtor_Passthrough_a0;
        unmatched63 = false;
        s = RAST.__default.RawType(_1448_v);
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
      for (BigInteger _1449_i = BigInteger.Zero; _1449_i < _hi26; _1449_i++) {
        DAST._IMethod _source67 = (body).Select(_1449_i);
        bool unmatched67 = true;
        if (unmatched67) {
          DAST._IMethod _1450_m = _source67;
          unmatched67 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source68 = (_1450_m).dtor_overridingPath;
            bool unmatched68 = true;
            if (unmatched68) {
              if (_source68.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1451_p = _source68.dtor_value;
                unmatched68 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1452_existing;
                  _1452_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1451_p)) {
                    _1452_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1451_p);
                  }
                  if (((new BigInteger(((_1450_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1453_genMethod;
                  RAST._IImplMember _out101;
                  _out101 = (this).GenMethod(_1450_m, true, enclosingType, enclosingTypeParams);
                  _1453_genMethod = _out101;
                  _1452_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1452_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1453_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1451_p, _1452_existing)));
                }
              }
            }
            if (unmatched68) {
              unmatched68 = false;
              {
                RAST._IImplMember _1454_generated;
                RAST._IImplMember _out102;
                _out102 = (this).GenMethod(_1450_m, forTrait, enclosingType, enclosingTypeParams);
                _1454_generated = _out102;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1454_generated));
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
      for (BigInteger _1455_i = BigInteger.Zero; _1455_i < _hi27; _1455_i++) {
        DAST._IFormal _1456_param;
        _1456_param = (@params).Select(_1455_i);
        RAST._IType _1457_paramType;
        RAST._IType _out103;
        _out103 = (this).GenType((_1456_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1457_paramType = _out103;
        if (((!((_1457_paramType).CanReadWithoutClone())) || (forLambda)) && (!((_1456_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1457_paramType = RAST.Type.create_Borrowed(_1457_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeVar((_1456_param).dtor_name), _1457_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1458_params;
      Dafny.ISequence<RAST._IFormal> _out104;
      _out104 = (this).GenParams((m).dtor_params, false);
      _1458_params = _out104;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1459_paramNames;
      _1459_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1460_paramTypes;
      _1460_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1461_paramI = BigInteger.Zero; _1461_paramI < _hi28; _1461_paramI++) {
        DAST._IFormal _1462_dafny__formal;
        _1462_dafny__formal = ((m).dtor_params).Select(_1461_paramI);
        RAST._IFormal _1463_formal;
        _1463_formal = (_1458_params).Select(_1461_paramI);
        Dafny.ISequence<Dafny.Rune> _1464_name;
        _1464_name = (_1463_formal).dtor_name;
        _1459_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1459_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1464_name));
        _1460_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1460_paramTypes, _1464_name, (_1463_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1465_fnName;
      _1465_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1466_selfIdent;
      _1466_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1467_selfId;
        _1467_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1467_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv142 = enclosingTypeParams;
        var _pat_let_tv143 = enclosingType;
        DAST._IType _1468_instanceType;
        _1468_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source69 = enclosingType;
          bool unmatched69 = true;
          if (unmatched69) {
            if (_source69.is_UserDefined) {
              DAST._IResolvedType _1469_r = _source69.dtor_resolved;
              unmatched69 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1469_r, _pat_let32_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let32_0, _1470_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv142, _pat_let33_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let33_0, _1471_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1470_dt__update__tmp_h0).dtor_path, _1471_dt__update_htypeArgs_h0, (_1470_dt__update__tmp_h0).dtor_kind, (_1470_dt__update__tmp_h0).dtor_attributes, (_1470_dt__update__tmp_h0).dtor_properMethods, (_1470_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched69) {
            unmatched69 = false;
            return _pat_let_tv143;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1472_selfFormal;
          _1472_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1458_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1472_selfFormal), _1458_params);
        } else {
          RAST._IType _1473_tpe;
          RAST._IType _out105;
          _out105 = (this).GenType(_1468_instanceType, DCOMP.GenTypeContext.@default());
          _1473_tpe = _out105;
          if ((_1467_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1473_tpe = RAST.Type.create_Borrowed(_1473_tpe);
          } else if ((_1467_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1473_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1473_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1473_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              if ((((enclosingType).is_UserDefined) && ((((enclosingType).dtor_resolved).dtor_kind).is_Datatype)) && ((this).IsRcWrapped(((enclosingType).dtor_resolved).dtor_attributes))) {
                _1473_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.Type.create_SelfOwned()));
              } else {
                _1473_tpe = RAST.Type.create_Borrowed(RAST.Type.create_SelfOwned());
              }
            }
          }
          _1458_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1467_selfId, _1473_tpe)), _1458_params);
        }
        _1466_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1467_selfId, _1468_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1474_retTypeArgs;
      _1474_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1475_typeI;
      _1475_typeI = BigInteger.Zero;
      while ((_1475_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1476_typeExpr;
        RAST._IType _out106;
        _out106 = (this).GenType(((m).dtor_outTypes).Select(_1475_typeI), DCOMP.GenTypeContext.@default());
        _1476_typeExpr = _out106;
        _1474_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1474_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1476_typeExpr));
        _1475_typeI = (_1475_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1477_visibility;
      _1477_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1478_typeParamsFiltered;
      _1478_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi29 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1479_typeParamI = BigInteger.Zero; _1479_typeParamI < _hi29; _1479_typeParamI++) {
        DAST._ITypeArgDecl _1480_typeParam;
        _1480_typeParam = ((m).dtor_typeParams).Select(_1479_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1480_typeParam).dtor_name)))) {
          _1478_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1478_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1480_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1481_typeParams;
      _1481_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1478_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi30 = new BigInteger((_1478_typeParamsFiltered).Count);
        for (BigInteger _1482_i = BigInteger.Zero; _1482_i < _hi30; _1482_i++) {
          DAST._IType _1483_typeArg;
          RAST._ITypeParamDecl _1484_rTypeParamDecl;
          DAST._IType _out107;
          RAST._ITypeParamDecl _out108;
          (this).GenTypeParam((_1478_typeParamsFiltered).Select(_1482_i), out _out107, out _out108);
          _1483_typeArg = _out107;
          _1484_rTypeParamDecl = _out108;
          var _pat_let_tv144 = _1484_rTypeParamDecl;
          _1484_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1484_rTypeParamDecl, _pat_let34_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let34_0, _1485_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv144).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let35_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let35_0, _1486_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1485_dt__update__tmp_h1).dtor_content, _1486_dt__update_hconstraints_h0)))));
          _1481_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1481_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1484_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1487_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1488_env = DCOMP.Environment.Default();
      RAST._IExpr _1489_preBody;
      _1489_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1490_preAssignNames;
      _1490_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1491_preAssignTypes;
      _1491_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1492_earlyReturn;
        _1492_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None();
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source70 = (m).dtor_outVars;
        bool unmatched70 = true;
        if (unmatched70) {
          if (_source70.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1493_outVars = _source70.dtor_value;
            unmatched70 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1492_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
                BigInteger _hi31 = new BigInteger((_1493_outVars).Count);
                for (BigInteger _1494_outI = BigInteger.Zero; _1494_outI < _hi31; _1494_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1495_outVar;
                  _1495_outVar = (_1493_outVars).Select(_1494_outI);
                  Dafny.ISequence<Dafny.Rune> _1496_outName;
                  _1496_outName = DCOMP.__default.escapeVar(_1495_outVar);
                  Dafny.ISequence<Dafny.Rune> _1497_tracker__name;
                  _1497_tracker__name = DCOMP.__default.AddAssignedPrefix(_1496_outName);
                  _1490_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1490_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1497_tracker__name));
                  _1491_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1491_preAssignTypes, _1497_tracker__name, RAST.Type.create_Bool());
                  _1489_preBody = (_1489_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1497_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1498_tupleArgs;
                _1498_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
                BigInteger _hi32 = new BigInteger((_1493_outVars).Count);
                for (BigInteger _1499_outI = BigInteger.Zero; _1499_outI < _hi32; _1499_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1500_outVar;
                  _1500_outVar = (_1493_outVars).Select(_1499_outI);
                  RAST._IType _1501_outType;
                  RAST._IType _out109;
                  _out109 = (this).GenType(((m).dtor_outTypes).Select(_1499_outI), DCOMP.GenTypeContext.@default());
                  _1501_outType = _out109;
                  Dafny.ISequence<Dafny.Rune> _1502_outName;
                  _1502_outName = DCOMP.__default.escapeVar(_1500_outVar);
                  _1459_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1459_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1502_outName));
                  RAST._IType _1503_outMaybeType;
                  _1503_outMaybeType = (((_1501_outType).CanReadWithoutClone()) ? (_1501_outType) : (RAST.__default.MaybePlaceboType(_1501_outType)));
                  _1460_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1460_paramTypes, _1502_outName, _1503_outMaybeType);
                  _1498_tupleArgs = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1498_tupleArgs, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1502_outName));
                }
                _1492_earlyReturn = Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_Some(_1498_tupleArgs);
              }
            }
          }
        }
        if (unmatched70) {
          unmatched70 = false;
        }
        _1488_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1490_preAssignNames, _1459_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1491_preAssignTypes, _1460_paramTypes));
        RAST._IExpr _1504_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1505___v69;
        DCOMP._IEnvironment _1506___v70;
        RAST._IExpr _out110;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
        DCOMP._IEnvironment _out112;
        (this).GenStmts((m).dtor_body, _1466_selfIdent, _1488_env, true, _1492_earlyReturn, out _out110, out _out111, out _out112);
        _1504_body = _out110;
        _1505___v69 = _out111;
        _1506___v70 = _out112;
        _1487_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1489_preBody).Then(_1504_body));
      } else {
        _1488_env = DCOMP.Environment.create(_1459_paramNames, _1460_paramTypes);
        _1487_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1477_visibility, RAST.Fn.create(_1465_fnName, _1481_typeParams, _1458_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1474_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1474_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1474_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1487_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1507_declarations;
      _1507_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1508_i;
      _1508_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1509_stmts;
      _1509_stmts = stmts;
      while ((_1508_i) < (new BigInteger((_1509_stmts).Count))) {
        DAST._IStatement _1510_stmt;
        _1510_stmt = (_1509_stmts).Select(_1508_i);
        DAST._IStatement _source71 = _1510_stmt;
        bool unmatched71 = true;
        if (unmatched71) {
          if (_source71.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1511_name = _source71.dtor_name;
            DAST._IType _1512_optType = _source71.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source71.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched71 = false;
              if (((_1508_i) + (BigInteger.One)) < (new BigInteger((_1509_stmts).Count))) {
                DAST._IStatement _source72 = (_1509_stmts).Select((_1508_i) + (BigInteger.One));
                bool unmatched72 = true;
                if (unmatched72) {
                  if (_source72.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source72.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> _1513_name2 = lhs0.dtor_ident;
                      DAST._IExpression _1514_rhs = _source72.dtor_value;
                      unmatched72 = false;
                      if (object.Equals(_1513_name2, _1511_name)) {
                        _1509_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1509_stmts).Subsequence(BigInteger.Zero, _1508_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1511_name, _1512_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1514_rhs)))), (_1509_stmts).Drop((_1508_i) + (new BigInteger(2))));
                        _1510_stmt = (_1509_stmts).Select(_1508_i);
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
        RAST._IExpr _1515_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1516_recIdents;
        DCOMP._IEnvironment _1517_newEnv2;
        RAST._IExpr _out113;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out114;
        DCOMP._IEnvironment _out115;
        (this).GenStmt(_1510_stmt, selfIdent, newEnv, (isLast) && ((_1508_i) == ((new BigInteger((_1509_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out113, out _out114, out _out115);
        _1515_stmtExpr = _out113;
        _1516_recIdents = _out114;
        _1517_newEnv2 = _out115;
        newEnv = _1517_newEnv2;
        DAST._IStatement _source73 = _1510_stmt;
        bool unmatched73 = true;
        if (unmatched73) {
          if (_source73.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1518_name = _source73.dtor_name;
            unmatched73 = false;
            {
              _1507_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1507_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_1518_name)));
            }
          }
        }
        if (unmatched73) {
          unmatched73 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1516_recIdents, _1507_declarations));
        generated = (generated).Then(_1515_stmtExpr);
        _1508_i = (_1508_i) + (BigInteger.One);
        if ((_1515_stmtExpr).is_Return) {
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
          Dafny.ISequence<Dafny.Rune> _1519_id = _source74.dtor_ident;
          unmatched74 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1520_idRust;
            _1520_idRust = DCOMP.__default.escapeVar(_1519_id);
            if (((env).IsBorrowed(_1520_idRust)) || ((env).IsBorrowedMut(_1520_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1520_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1520_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1520_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Select) {
          DAST._IExpression _1521_on = _source74.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1522_field = _source74.dtor_field;
          unmatched74 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1523_fieldName;
            _1523_fieldName = DCOMP.__default.escapeVar(_1522_field);
            RAST._IExpr _1524_onExpr;
            DCOMP._IOwnership _1525_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1526_recIdents;
            RAST._IExpr _out116;
            DCOMP._IOwnership _out117;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out118;
            (this).GenExpr(_1521_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out116, out _out117, out _out118);
            _1524_onExpr = _out116;
            _1525_onOwned = _out117;
            _1526_recIdents = _out118;
            RAST._IExpr _source75 = _1524_onExpr;
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
                Dafny.ISequence<Dafny.Rune> _1527_isAssignedVar;
                _1527_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1523_fieldName);
                if (((newEnv).dtor_names).Contains(_1527_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1523_fieldName), RAST.Expr.create_Identifier(_1527_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1527_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1527_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1523_fieldName, rhs);
                }
              }
            }
            if (unmatched75) {
              unmatched75 = false;
              if (!object.Equals(_1524_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1524_onExpr = ((this).modify__macro).Apply1(_1524_onExpr);
              }
              generated = RAST.__default.AssignMember(_1524_onExpr, _1523_fieldName, rhs);
            }
            readIdents = _1526_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched74) {
        DAST._IExpression _1528_on = _source74.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1529_indices = _source74.dtor_indices;
        unmatched74 = false;
        {
          RAST._IExpr _1530_onExpr;
          DCOMP._IOwnership _1531_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1532_recIdents;
          RAST._IExpr _out119;
          DCOMP._IOwnership _out120;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out121;
          (this).GenExpr(_1528_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out119, out _out120, out _out121);
          _1530_onExpr = _out119;
          _1531_onOwned = _out120;
          _1532_recIdents = _out121;
          readIdents = _1532_recIdents;
          _1530_onExpr = ((this).modify__macro).Apply1(_1530_onExpr);
          RAST._IExpr _1533_r;
          _1533_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1534_indicesExpr;
          _1534_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi33 = new BigInteger((_1529_indices).Count);
          for (BigInteger _1535_i = BigInteger.Zero; _1535_i < _hi33; _1535_i++) {
            RAST._IExpr _1536_idx;
            DCOMP._IOwnership _1537___v79;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1538_recIdentsIdx;
            RAST._IExpr _out122;
            DCOMP._IOwnership _out123;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out124;
            (this).GenExpr((_1529_indices).Select(_1535_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out122, out _out123, out _out124);
            _1536_idx = _out122;
            _1537___v79 = _out123;
            _1538_recIdentsIdx = _out124;
            Dafny.ISequence<Dafny.Rune> _1539_varName;
            _1539_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1535_i));
            _1534_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1534_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1539_varName)));
            _1533_r = (_1533_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1539_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.IntoUsize(_1536_idx))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1538_recIdentsIdx);
          }
          if ((new BigInteger((_1529_indices).Count)) > (BigInteger.One)) {
            _1530_onExpr = (_1530_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1540_rhs;
          _1540_rhs = rhs;
          var _pat_let_tv145 = env;
          if (((_1530_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1530_onExpr).LhsIdentifierName(), _pat_let36_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let36_0, _1541_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv145).GetType(_1541_name), _pat_let37_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let37_0, _1542_tpe => ((_1542_tpe).is_Some) && (((_1542_tpe).dtor_value).IsUninitArray())))))))) {
            _1540_rhs = RAST.__default.MaybeUninitNew(_1540_rhs);
          }
          generated = (_1533_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1530_onExpr, _1534_indicesExpr)), _1540_rhs));
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
          Dafny.ISequence<DAST._IFormal> _1543_fields = _source76.dtor_fields;
          unmatched76 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi34 = new BigInteger((_1543_fields).Count);
            for (BigInteger _1544_i = BigInteger.Zero; _1544_i < _hi34; _1544_i++) {
              DAST._IFormal _1545_field;
              _1545_field = (_1543_fields).Select(_1544_i);
              Dafny.ISequence<Dafny.Rune> _1546_fieldName;
              _1546_fieldName = DCOMP.__default.escapeVar((_1545_field).dtor_name);
              RAST._IType _1547_fieldTyp;
              RAST._IType _out125;
              _out125 = (this).GenType((_1545_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1547_fieldTyp = _out125;
              Dafny.ISequence<Dafny.Rune> _1548_isAssignedVar;
              _1548_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1546_fieldName);
              if (((newEnv).dtor_names).Contains(_1548_isAssignedVar)) {
                RAST._IExpr _1549_rhs;
                DCOMP._IOwnership _1550___v80;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1551___v81;
                RAST._IExpr _out126;
                DCOMP._IOwnership _out127;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out128;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1545_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out126, out _out127, out _out128);
                _1549_rhs = _out126;
                _1550___v80 = _out127;
                _1551___v81 = _out128;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1548_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1546_fieldName), RAST.Expr.create_Identifier(_1548_isAssignedVar), _1549_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1548_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1552_name = _source76.dtor_name;
          DAST._IType _1553_typ = _source76.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source76.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1554_expression = maybeValue1.dtor_value;
            unmatched76 = false;
            {
              RAST._IType _1555_tpe;
              RAST._IType _out129;
              _out129 = (this).GenType(_1553_typ, DCOMP.GenTypeContext.InBinding());
              _1555_tpe = _out129;
              Dafny.ISequence<Dafny.Rune> _1556_varName;
              _1556_varName = DCOMP.__default.escapeVar(_1552_name);
              bool _1557_hasCopySemantics;
              _1557_hasCopySemantics = (_1555_tpe).CanReadWithoutClone();
              if (((_1554_expression).is_InitializationValue) && (!(_1557_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1556_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1555_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1556_varName, RAST.__default.MaybePlaceboType(_1555_tpe));
              } else {
                RAST._IExpr _1558_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1559_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1554_expression).is_InitializationValue) && ((_1555_tpe).IsObjectOrPointer())) {
                  _1558_expr = (_1555_tpe).ToNullExpr();
                  _1559_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1560_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out130;
                  DCOMP._IOwnership _out131;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out132;
                  (this).GenExpr(_1554_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out130, out _out131, out _out132);
                  _1558_expr = _out130;
                  _1560_exprOwnership = _out131;
                  _1559_recIdents = _out132;
                }
                readIdents = _1559_recIdents;
                _1555_tpe = (((_1554_expression).is_NewUninitArray) ? ((_1555_tpe).TypeAtInitialization()) : (_1555_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1556_varName, Std.Wrappers.Option<RAST._IType>.create_Some(_1555_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1558_expr));
                newEnv = (env).AddAssigned(_1556_varName, _1555_tpe);
              }
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1561_name = _source76.dtor_name;
          DAST._IType _1562_typ = _source76.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source76.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched76 = false;
            {
              DAST._IStatement _1563_newStmt;
              _1563_newStmt = DAST.Statement.create_DeclareVar(_1561_name, _1562_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1562_typ)));
              RAST._IExpr _out133;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out134;
              DCOMP._IEnvironment _out135;
              (this).GenStmt(_1563_newStmt, selfIdent, env, isLast, earlyReturn, out _out133, out _out134, out _out135);
              generated = _out133;
              readIdents = _out134;
              newEnv = _out135;
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Assign) {
          DAST._IAssignLhs _1564_lhs = _source76.dtor_lhs;
          DAST._IExpression _1565_expression = _source76.dtor_value;
          unmatched76 = false;
          {
            RAST._IExpr _1566_exprGen;
            DCOMP._IOwnership _1567___v82;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1568_exprIdents;
            RAST._IExpr _out136;
            DCOMP._IOwnership _out137;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out138;
            (this).GenExpr(_1565_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out136, out _out137, out _out138);
            _1566_exprGen = _out136;
            _1567___v82 = _out137;
            _1568_exprIdents = _out138;
            if ((_1564_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1569_rustId;
              _1569_rustId = DCOMP.__default.escapeVar((_1564_lhs).dtor_ident);
              Std.Wrappers._IOption<RAST._IType> _1570_tpe;
              _1570_tpe = (env).GetType(_1569_rustId);
              if (((_1570_tpe).is_Some) && ((((_1570_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1566_exprGen = RAST.__default.MaybePlacebo(_1566_exprGen);
              }
            }
            if (((_1564_lhs).is_Index) && (((_1564_lhs).dtor_expr).is_Ident)) {
              Dafny.ISequence<Dafny.Rune> _1571_rustId;
              _1571_rustId = DCOMP.__default.escapeVar(((_1564_lhs).dtor_expr).dtor_name);
              Std.Wrappers._IOption<RAST._IType> _1572_tpe;
              _1572_tpe = (env).GetType(_1571_rustId);
              if (((_1572_tpe).is_Some) && ((((_1572_tpe).dtor_value).ExtractMaybeUninitArrayElement()).is_Some)) {
                _1566_exprGen = RAST.__default.MaybeUninitNew(_1566_exprGen);
              }
            }
            RAST._IExpr _1573_lhsGen;
            bool _1574_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1575_recIdents;
            DCOMP._IEnvironment _1576_resEnv;
            RAST._IExpr _out139;
            bool _out140;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out141;
            DCOMP._IEnvironment _out142;
            (this).GenAssignLhs(_1564_lhs, _1566_exprGen, selfIdent, env, out _out139, out _out140, out _out141, out _out142);
            _1573_lhsGen = _out139;
            _1574_needsIIFE = _out140;
            _1575_recIdents = _out141;
            _1576_resEnv = _out142;
            generated = _1573_lhsGen;
            newEnv = _1576_resEnv;
            if (_1574_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1575_recIdents, _1568_exprIdents);
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_If) {
          DAST._IExpression _1577_cond = _source76.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1578_thnDafny = _source76.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1579_elsDafny = _source76.dtor_els;
          unmatched76 = false;
          {
            RAST._IExpr _1580_cond;
            DCOMP._IOwnership _1581___v83;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1582_recIdents;
            RAST._IExpr _out143;
            DCOMP._IOwnership _out144;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out145;
            (this).GenExpr(_1577_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out143, out _out144, out _out145);
            _1580_cond = _out143;
            _1581___v83 = _out144;
            _1582_recIdents = _out145;
            Dafny.ISequence<Dafny.Rune> _1583_condString;
            _1583_condString = (_1580_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1582_recIdents;
            RAST._IExpr _1584_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1585_thnIdents;
            DCOMP._IEnvironment _1586_thnEnv;
            RAST._IExpr _out146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
            DCOMP._IEnvironment _out148;
            (this).GenStmts(_1578_thnDafny, selfIdent, env, isLast, earlyReturn, out _out146, out _out147, out _out148);
            _1584_thn = _out146;
            _1585_thnIdents = _out147;
            _1586_thnEnv = _out148;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1585_thnIdents);
            RAST._IExpr _1587_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1588_elsIdents;
            DCOMP._IEnvironment _1589_elsEnv;
            RAST._IExpr _out149;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out150;
            DCOMP._IEnvironment _out151;
            (this).GenStmts(_1579_elsDafny, selfIdent, env, isLast, earlyReturn, out _out149, out _out150, out _out151);
            _1587_els = _out149;
            _1588_elsIdents = _out150;
            _1589_elsEnv = _out151;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1588_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1580_cond, _1584_thn, _1587_els);
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1590_lbl = _source76.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1591_body = _source76.dtor_body;
          unmatched76 = false;
          {
            RAST._IExpr _1592_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1593_bodyIdents;
            DCOMP._IEnvironment _1594_env2;
            RAST._IExpr _out152;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out153;
            DCOMP._IEnvironment _out154;
            (this).GenStmts(_1591_body, selfIdent, env, isLast, earlyReturn, out _out152, out _out153, out _out154);
            _1592_body = _out152;
            _1593_bodyIdents = _out153;
            _1594_env2 = _out154;
            readIdents = _1593_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1590_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1592_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_While) {
          DAST._IExpression _1595_cond = _source76.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1596_body = _source76.dtor_body;
          unmatched76 = false;
          {
            RAST._IExpr _1597_cond;
            DCOMP._IOwnership _1598___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1599_recIdents;
            RAST._IExpr _out155;
            DCOMP._IOwnership _out156;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out157;
            (this).GenExpr(_1595_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out155, out _out156, out _out157);
            _1597_cond = _out155;
            _1598___v84 = _out156;
            _1599_recIdents = _out157;
            readIdents = _1599_recIdents;
            RAST._IExpr _1600_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1601_bodyIdents;
            DCOMP._IEnvironment _1602_bodyEnv;
            RAST._IExpr _out158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
            DCOMP._IEnvironment _out160;
            (this).GenStmts(_1596_body, selfIdent, env, false, earlyReturn, out _out158, out _out159, out _out160);
            _1600_bodyExpr = _out158;
            _1601_bodyIdents = _out159;
            _1602_bodyEnv = _out160;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1601_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1597_cond), _1600_bodyExpr);
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1603_boundName = _source76.dtor_boundName;
          DAST._IType _1604_boundType = _source76.dtor_boundType;
          DAST._IExpression _1605_overExpr = _source76.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1606_body = _source76.dtor_body;
          unmatched76 = false;
          {
            RAST._IExpr _1607_over;
            DCOMP._IOwnership _1608___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1609_recIdents;
            RAST._IExpr _out161;
            DCOMP._IOwnership _out162;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out163;
            (this).GenExpr(_1605_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out161, out _out162, out _out163);
            _1607_over = _out161;
            _1608___v85 = _out162;
            _1609_recIdents = _out163;
            if (((_1605_overExpr).is_MapBoundedPool) || ((_1605_overExpr).is_SetBoundedPool)) {
              _1607_over = ((_1607_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1610_boundTpe;
            RAST._IType _out164;
            _out164 = (this).GenType(_1604_boundType, DCOMP.GenTypeContext.@default());
            _1610_boundTpe = _out164;
            readIdents = _1609_recIdents;
            Dafny.ISequence<Dafny.Rune> _1611_boundRName;
            _1611_boundRName = DCOMP.__default.escapeVar(_1603_boundName);
            RAST._IExpr _1612_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1613_bodyIdents;
            DCOMP._IEnvironment _1614_bodyEnv;
            RAST._IExpr _out165;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out166;
            DCOMP._IEnvironment _out167;
            (this).GenStmts(_1606_body, selfIdent, (env).AddAssigned(_1611_boundRName, _1610_boundTpe), false, earlyReturn, out _out165, out _out166, out _out167);
            _1612_bodyExpr = _out165;
            _1613_bodyIdents = _out166;
            _1614_bodyEnv = _out167;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1613_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1611_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1611_boundRName, _1607_over, _1612_bodyExpr);
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1615_toLabel = _source76.dtor_toLabel;
          unmatched76 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source77 = _1615_toLabel;
            bool unmatched77 = true;
            if (unmatched77) {
              if (_source77.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1616_lbl = _source77.dtor_value;
                unmatched77 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1616_lbl)));
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
          Dafny.ISequence<DAST._IStatement> _1617_body = _source76.dtor_body;
          unmatched76 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1618_selfClone;
              DCOMP._IOwnership _1619___v86;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1620___v87;
              RAST._IExpr _out168;
              DCOMP._IOwnership _out169;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out170;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out168, out _out169, out _out170);
              _1618_selfClone = _out168;
              _1619___v86 = _out169;
              _1620___v87 = _out170;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1618_selfClone)));
            }
            newEnv = env;
            BigInteger _hi35 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1621_paramI = BigInteger.Zero; _1621_paramI < _hi35; _1621_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1622_param;
              _1622_param = ((env).dtor_names).Select(_1621_paramI);
              RAST._IExpr _1623_paramInit;
              DCOMP._IOwnership _1624___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1625___v89;
              RAST._IExpr _out171;
              DCOMP._IOwnership _out172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
              (this).GenIdent(_1622_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out171, out _out172, out _out173);
              _1623_paramInit = _out171;
              _1624___v88 = _out172;
              _1625___v89 = _out173;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1622_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1623_paramInit)));
              if (((env).dtor_types).Contains(_1622_param)) {
                RAST._IType _1626_declaredType;
                _1626_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1622_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1622_param, _1626_declaredType);
              }
            }
            RAST._IExpr _1627_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1628_bodyIdents;
            DCOMP._IEnvironment _1629_bodyEnv;
            RAST._IExpr _out174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out175;
            DCOMP._IEnvironment _out176;
            (this).GenStmts(_1617_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out174, out _out175, out _out176);
            _1627_bodyExpr = _out174;
            _1628_bodyIdents = _out175;
            _1629_bodyEnv = _out176;
            readIdents = _1628_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1627_bodyExpr)));
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
          DAST._IExpression _1630_on = _source76.dtor_on;
          DAST._ICallName _1631_name = _source76.dtor_callName;
          Dafny.ISequence<DAST._IType> _1632_typeArgs = _source76.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1633_args = _source76.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1634_maybeOutVars = _source76.dtor_outs;
          unmatched76 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1635_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1636_recIdents;
            Dafny.ISequence<RAST._IType> _1637_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1638_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out178;
            Dafny.ISequence<RAST._IType> _out179;
            Std.Wrappers._IOption<DAST._IResolvedType> _out180;
            (this).GenArgs(selfIdent, _1631_name, _1632_typeArgs, _1633_args, env, out _out177, out _out178, out _out179, out _out180);
            _1635_argExprs = _out177;
            _1636_recIdents = _out178;
            _1637_typeExprs = _out179;
            _1638_fullNameQualifier = _out180;
            readIdents = _1636_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source78 = _1638_fullNameQualifier;
            bool unmatched78 = true;
            if (unmatched78) {
              if (_source78.is_Some) {
                DAST._IResolvedType value9 = _source78.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1639_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1640_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1641_base = value9.dtor_kind;
                unmatched78 = false;
                RAST._IExpr _1642_fullPath;
                RAST._IExpr _out181;
                _out181 = DCOMP.COMP.GenPathExpr(_1639_path, true);
                _1642_fullPath = _out181;
                Dafny.ISequence<RAST._IType> _1643_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out182;
                _out182 = (this).GenTypeArgs(_1640_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1643_onTypeExprs = _out182;
                RAST._IExpr _1644_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1645_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1646_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1641_base).is_Trait) || ((_1641_base).is_Class)) {
                  RAST._IExpr _out183;
                  DCOMP._IOwnership _out184;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out185;
                  (this).GenExpr(_1630_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out183, out _out184, out _out185);
                  _1644_onExpr = _out183;
                  _1645_recOwnership = _out184;
                  _1646_recIdents = _out185;
                  _1644_onExpr = ((this).modify__macro).Apply1(_1644_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1646_recIdents);
                } else {
                  RAST._IExpr _out186;
                  DCOMP._IOwnership _out187;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out188;
                  (this).GenExpr(_1630_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out186, out _out187, out _out188);
                  _1644_onExpr = _out186;
                  _1645_recOwnership = _out187;
                  _1646_recIdents = _out188;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1646_recIdents);
                }
                generated = ((((_1642_fullPath).ApplyType(_1643_onTypeExprs)).MSel(DCOMP.__default.escapeName((_1631_name).dtor_name))).ApplyType(_1637_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1644_onExpr), _1635_argExprs));
              }
            }
            if (unmatched78) {
              unmatched78 = false;
              RAST._IExpr _1647_onExpr;
              DCOMP._IOwnership _1648___v94;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1649_enclosingIdents;
              RAST._IExpr _out189;
              DCOMP._IOwnership _out190;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out191;
              (this).GenExpr(_1630_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out189, out _out190, out _out191);
              _1647_onExpr = _out189;
              _1648___v94 = _out190;
              _1649_enclosingIdents = _out191;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1649_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1650_renderedName;
              _1650_renderedName = (this).GetMethodName(_1630_on, _1631_name);
              DAST._IExpression _source79 = _1630_on;
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
                    _1647_onExpr = (_1647_onExpr).MSel(_1650_renderedName);
                  }
                }
              }
              if (unmatched79) {
                unmatched79 = false;
                {
                  if (!object.Equals(_1647_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source80 = _1631_name;
                    bool unmatched80 = true;
                    if (unmatched80) {
                      if (_source80.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source80.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1651_tpe = onType0.dtor_value;
                          unmatched80 = false;
                          RAST._IType _1652_typ;
                          RAST._IType _out192;
                          _out192 = (this).GenType(_1651_tpe, DCOMP.GenTypeContext.@default());
                          _1652_typ = _out192;
                          if (((_1652_typ).IsObjectOrPointer()) && (!object.Equals(_1647_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1647_onExpr = ((this).modify__macro).Apply1(_1647_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched80) {
                      unmatched80 = false;
                    }
                  }
                  _1647_onExpr = (_1647_onExpr).Sel(_1650_renderedName);
                }
              }
              generated = ((_1647_onExpr).ApplyType(_1637_typeExprs)).Apply(_1635_argExprs);
            }
            if (((_1634_maybeOutVars).is_Some) && ((new BigInteger(((_1634_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1653_outVar;
              _1653_outVar = DCOMP.__default.escapeVar(((_1634_maybeOutVars).dtor_value).Select(BigInteger.Zero));
              if (!((env).CanReadWithoutClone(_1653_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1653_outVar, generated);
            } else if (((_1634_maybeOutVars).is_None) || ((new BigInteger(((_1634_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1654_tmpVar;
              _1654_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1655_tmpId;
              _1655_tmpId = RAST.Expr.create_Identifier(_1654_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1654_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1656_outVars;
              _1656_outVars = (_1634_maybeOutVars).dtor_value;
              BigInteger _hi36 = new BigInteger((_1656_outVars).Count);
              for (BigInteger _1657_outI = BigInteger.Zero; _1657_outI < _hi36; _1657_outI++) {
                Dafny.ISequence<Dafny.Rune> _1658_outVar;
                _1658_outVar = DCOMP.__default.escapeVar((_1656_outVars).Select(_1657_outI));
                RAST._IExpr _1659_rhs;
                _1659_rhs = (_1655_tmpId).Sel(Std.Strings.__default.OfNat(_1657_outI));
                if (!((env).CanReadWithoutClone(_1658_outVar))) {
                  _1659_rhs = RAST.__default.MaybePlacebo(_1659_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1658_outVar, _1659_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Return) {
          DAST._IExpression _1660_exprDafny = _source76.dtor_expr;
          unmatched76 = false;
          {
            RAST._IExpr _1661_expr;
            DCOMP._IOwnership _1662___v104;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1663_recIdents;
            RAST._IExpr _out193;
            DCOMP._IOwnership _out194;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out195;
            (this).GenExpr(_1660_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out193, out _out194, out _out195);
            _1661_expr = _out193;
            _1662___v104 = _out194;
            _1663_recIdents = _out195;
            readIdents = _1663_recIdents;
            if (isLast) {
              generated = _1661_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1661_expr));
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
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1664_rustIdents = _source81.dtor_value;
              unmatched81 = false;
              Dafny.ISequence<RAST._IExpr> _1665_tupleArgs;
              _1665_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi37 = new BigInteger((_1664_rustIdents).Count);
              for (BigInteger _1666_i = BigInteger.Zero; _1666_i < _hi37; _1666_i++) {
                RAST._IExpr _1667_rIdent;
                DCOMP._IOwnership _1668___v105;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1669___v106;
                RAST._IExpr _out196;
                DCOMP._IOwnership _out197;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out198;
                (this).GenIdent((_1664_rustIdents).Select(_1666_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out196, out _out197, out _out198);
                _1667_rIdent = _out196;
                _1668___v105 = _out197;
                _1669___v106 = _out198;
                _1665_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1665_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1667_rIdent));
              }
              if ((new BigInteger((_1665_tupleArgs).Count)) == (BigInteger.One)) {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1665_tupleArgs).Select(BigInteger.Zero)));
              } else {
                generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1665_tupleArgs)));
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
        DAST._IExpression _1670_e = _source76.dtor_Print_a0;
        unmatched76 = false;
        {
          RAST._IExpr _1671_printedExpr;
          DCOMP._IOwnership _1672_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1673_recIdents;
          RAST._IExpr _out199;
          DCOMP._IOwnership _out200;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out201;
          (this).GenExpr(_1670_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out199, out _out200, out _out201);
          _1671_printedExpr = _out199;
          _1672_recOwnership = _out200;
          _1673_recIdents = _out201;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1671_printedExpr)));
          readIdents = _1673_recIdents;
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
            bool _1674_b = _h170.dtor_BoolLiteral_a0;
            unmatched83 = false;
            {
              RAST._IExpr _out206;
              DCOMP._IOwnership _out207;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1674_b), expectedOwnership, out _out206, out _out207);
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
            Dafny.ISequence<Dafny.Rune> _1675_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1676_t = _h171.dtor_IntLiteral_a1;
            unmatched83 = false;
            {
              DAST._IType _source84 = _1676_t;
              bool unmatched84 = true;
              if (unmatched84) {
                if (_source84.is_Primitive) {
                  DAST._IPrimitive _h70 = _source84.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched84 = false;
                    {
                      if ((new BigInteger((_1675_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1675_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1675_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched84) {
                DAST._IType _1677_o = _source84;
                unmatched84 = false;
                {
                  RAST._IType _1678_genType;
                  RAST._IType _out208;
                  _out208 = (this).GenType(_1677_o, DCOMP.GenTypeContext.@default());
                  _1678_genType = _out208;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1675_i), _1678_genType);
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
            Dafny.ISequence<Dafny.Rune> _1679_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1680_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1681_t = _h172.dtor_DecLiteral_a2;
            unmatched83 = false;
            {
              DAST._IType _source85 = _1681_t;
              bool unmatched85 = true;
              if (unmatched85) {
                if (_source85.is_Primitive) {
                  DAST._IPrimitive _h71 = _source85.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched85 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1679_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1680_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched85) {
                DAST._IType _1682_o = _source85;
                unmatched85 = false;
                {
                  RAST._IType _1683_genType;
                  RAST._IType _out211;
                  _out211 = (this).GenType(_1682_o, DCOMP.GenTypeContext.@default());
                  _1683_genType = _out211;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1679_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1680_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1683_genType);
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
            Dafny.ISequence<Dafny.Rune> _1684_l = _h173.dtor_StringLiteral_a0;
            bool _1685_verbatim = _h173.dtor_verbatim;
            unmatched83 = false;
            {
              if (_1685_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1684_l, false, _1685_verbatim));
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
            BigInteger _1686_c = _h174.dtor_CharLiteralUTF16_a0;
            unmatched83 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1686_c));
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
            Dafny.Rune _1687_c = _h175.dtor_CharLiteral_a0;
            unmatched83 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1687_c).Value)));
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
        DAST._IType _1688_tpe = _h176.dtor_Null_a0;
        unmatched83 = false;
        {
          RAST._IType _1689_tpeGen;
          RAST._IType _out220;
          _out220 = (this).GenType(_1688_tpe, DCOMP.GenTypeContext.@default());
          _1689_tpeGen = _out220;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"));
          } else {
            r = RAST.Expr.create_TypeAscription(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1689_tpeGen);
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
      DAST._IBinOp _1690_op = _let_tmp_rhs54.dtor_op;
      DAST._IExpression _1691_lExpr = _let_tmp_rhs54.dtor_left;
      DAST._IExpression _1692_rExpr = _let_tmp_rhs54.dtor_right;
      DAST.Format._IBinaryOpFormat _1693_format = _let_tmp_rhs54.dtor_format2;
      bool _1694_becomesLeftCallsRight;
      _1694_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source86 = _1690_op;
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
      bool _1695_becomesRightCallsLeft;
      _1695_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source87 = _1690_op;
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
      bool _1696_becomesCallLeftRight;
      _1696_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source88 = _1690_op;
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
      DCOMP._IOwnership _1697_expectedLeftOwnership;
      _1697_expectedLeftOwnership = ((_1694_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1695_becomesRightCallsLeft) || (_1696_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1698_expectedRightOwnership;
      _1698_expectedRightOwnership = (((_1694_becomesLeftCallsRight) || (_1696_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1695_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1699_left;
      DCOMP._IOwnership _1700___v111;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1701_recIdentsL;
      RAST._IExpr _out223;
      DCOMP._IOwnership _out224;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out225;
      (this).GenExpr(_1691_lExpr, selfIdent, env, _1697_expectedLeftOwnership, out _out223, out _out224, out _out225);
      _1699_left = _out223;
      _1700___v111 = _out224;
      _1701_recIdentsL = _out225;
      RAST._IExpr _1702_right;
      DCOMP._IOwnership _1703___v112;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1704_recIdentsR;
      RAST._IExpr _out226;
      DCOMP._IOwnership _out227;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
      (this).GenExpr(_1692_rExpr, selfIdent, env, _1698_expectedRightOwnership, out _out226, out _out227, out _out228);
      _1702_right = _out226;
      _1703___v112 = _out227;
      _1704_recIdentsR = _out228;
      DAST._IBinOp _source89 = _1690_op;
      bool unmatched89 = true;
      if (unmatched89) {
        if (_source89.is_In) {
          unmatched89 = false;
          {
            r = ((_1702_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1699_left);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_SeqProperPrefix) {
          unmatched89 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1699_left, _1702_right, _1693_format);
        }
      }
      if (unmatched89) {
        if (_source89.is_SeqPrefix) {
          unmatched89 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1699_left, _1702_right, _1693_format);
        }
      }
      if (unmatched89) {
        if (_source89.is_SetMerge) {
          unmatched89 = false;
          {
            r = ((_1699_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1702_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_SetSubtraction) {
          unmatched89 = false;
          {
            r = ((_1699_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1702_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_SetIntersection) {
          unmatched89 = false;
          {
            r = ((_1699_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1702_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Subset) {
          unmatched89 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1699_left, _1702_right, _1693_format);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_ProperSubset) {
          unmatched89 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1699_left, _1702_right, _1693_format);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_SetDisjoint) {
          unmatched89 = false;
          {
            r = ((_1699_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1702_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_MapMerge) {
          unmatched89 = false;
          {
            r = ((_1699_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1702_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_MapSubtraction) {
          unmatched89 = false;
          {
            r = ((_1699_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1702_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_MultisetMerge) {
          unmatched89 = false;
          {
            r = ((_1699_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1702_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_MultisetSubtraction) {
          unmatched89 = false;
          {
            r = ((_1699_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1702_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_MultisetIntersection) {
          unmatched89 = false;
          {
            r = ((_1699_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1702_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Submultiset) {
          unmatched89 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1699_left, _1702_right, _1693_format);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_ProperSubmultiset) {
          unmatched89 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1699_left, _1702_right, _1693_format);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_MultisetDisjoint) {
          unmatched89 = false;
          {
            r = ((_1699_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1702_right);
          }
        }
      }
      if (unmatched89) {
        if (_source89.is_Concat) {
          unmatched89 = false;
          {
            r = ((_1699_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1702_right);
          }
        }
      }
      if (unmatched89) {
        unmatched89 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1690_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1690_op), _1699_left, _1702_right, _1693_format);
          } else {
            DAST._IBinOp _source90 = _1690_op;
            bool unmatched90 = true;
            if (unmatched90) {
              if (_source90.is_Eq) {
                bool _1705_referential = _source90.dtor_referential;
                unmatched90 = false;
                {
                  if (_1705_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1699_left, _1702_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1692_rExpr).is_SeqValue) && ((new BigInteger(((_1692_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1699_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1691_lExpr).is_SeqValue) && ((new BigInteger(((_1691_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1702_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1699_left, _1702_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched90) {
              if (_source90.is_EuclidianDiv) {
                unmatched90 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1699_left, _1702_right));
                }
              }
            }
            if (unmatched90) {
              if (_source90.is_EuclidianMod) {
                unmatched90 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1699_left, _1702_right));
                }
              }
            }
            if (unmatched90) {
              Dafny.ISequence<Dafny.Rune> _1706_op = _source90.dtor_Passthrough_a0;
              unmatched90 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1706_op, _1699_left, _1702_right, _1693_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1701_recIdentsL, _1704_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs55 = e;
      DAST._IExpression _1707_expr = _let_tmp_rhs55.dtor_value;
      DAST._IType _1708_fromTpe = _let_tmp_rhs55.dtor_from;
      DAST._IType _1709_toTpe = _let_tmp_rhs55.dtor_typ;
      DAST._IType _let_tmp_rhs56 = _1709_toTpe;
      DAST._IResolvedType _let_tmp_rhs57 = _let_tmp_rhs56.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1710_path = _let_tmp_rhs57.dtor_path;
      Dafny.ISequence<DAST._IType> _1711_typeArgs = _let_tmp_rhs57.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs58 = _let_tmp_rhs57.dtor_kind;
      DAST._IType _1712_b = _let_tmp_rhs58.dtor_baseType;
      DAST._INewtypeRange _1713_range = _let_tmp_rhs58.dtor_range;
      bool _1714_erase = _let_tmp_rhs58.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1715___v114 = _let_tmp_rhs57.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1716___v115 = _let_tmp_rhs57.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1717___v116 = _let_tmp_rhs57.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1718_nativeToType;
      _1718_nativeToType = DCOMP.COMP.NewtypeRangeToRustType(_1713_range);
      if (object.Equals(_1708_fromTpe, _1712_b)) {
        RAST._IExpr _1719_recursiveGen;
        DCOMP._IOwnership _1720_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1721_recIdents;
        RAST._IExpr _out231;
        DCOMP._IOwnership _out232;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out233;
        (this).GenExpr(_1707_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out231, out _out232, out _out233);
        _1719_recursiveGen = _out231;
        _1720_recOwned = _out232;
        _1721_recIdents = _out233;
        readIdents = _1721_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source91 = _1718_nativeToType;
        bool unmatched91 = true;
        if (unmatched91) {
          if (_source91.is_Some) {
            RAST._IType _1722_v = _source91.dtor_value;
            unmatched91 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1719_recursiveGen, RAST.Expr.create_ExprFromType(_1722_v)));
            RAST._IExpr _out234;
            DCOMP._IOwnership _out235;
            (this).FromOwned(r, expectedOwnership, out _out234, out _out235);
            r = _out234;
            resultingOwnership = _out235;
          }
        }
        if (unmatched91) {
          unmatched91 = false;
          if (_1714_erase) {
            r = _1719_recursiveGen;
          } else {
            RAST._IType _1723_rhsType;
            RAST._IType _out236;
            _out236 = (this).GenType(_1709_toTpe, DCOMP.GenTypeContext.InBinding());
            _1723_rhsType = _out236;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1723_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1719_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out237;
          DCOMP._IOwnership _out238;
          (this).FromOwnership(r, _1720_recOwned, expectedOwnership, out _out237, out _out238);
          r = _out237;
          resultingOwnership = _out238;
        }
      } else {
        if ((_1718_nativeToType).is_Some) {
          DAST._IType _source92 = _1708_fromTpe;
          bool unmatched92 = true;
          if (unmatched92) {
            if (_source92.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source92.dtor_resolved;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1724_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1725_range0 = kind1.dtor_range;
                bool _1726_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1727_attributes0 = resolved1.dtor_attributes;
                unmatched92 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1728_nativeFromType;
                  _1728_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1725_range0);
                  if ((_1728_nativeFromType).is_Some) {
                    RAST._IExpr _1729_recursiveGen;
                    DCOMP._IOwnership _1730_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1731_recIdents;
                    RAST._IExpr _out239;
                    DCOMP._IOwnership _out240;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out241;
                    (this).GenExpr(_1707_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out239, out _out240, out _out241);
                    _1729_recursiveGen = _out239;
                    _1730_recOwned = _out240;
                    _1731_recIdents = _out241;
                    RAST._IExpr _out242;
                    DCOMP._IOwnership _out243;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1729_recursiveGen, (_1718_nativeToType).dtor_value), _1730_recOwned, expectedOwnership, out _out242, out _out243);
                    r = _out242;
                    resultingOwnership = _out243;
                    readIdents = _1731_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched92) {
            unmatched92 = false;
          }
          if (object.Equals(_1708_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1732_recursiveGen;
            DCOMP._IOwnership _1733_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1734_recIdents;
            RAST._IExpr _out244;
            DCOMP._IOwnership _out245;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out246;
            (this).GenExpr(_1707_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out244, out _out245, out _out246);
            _1732_recursiveGen = _out244;
            _1733_recOwned = _out245;
            _1734_recIdents = _out246;
            RAST._IExpr _out247;
            DCOMP._IOwnership _out248;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1732_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1718_nativeToType).dtor_value), _1733_recOwned, expectedOwnership, out _out247, out _out248);
            r = _out247;
            resultingOwnership = _out248;
            readIdents = _1734_recIdents;
            return ;
          }
        }
        RAST._IExpr _out249;
        DCOMP._IOwnership _out250;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out251;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1707_expr, _1708_fromTpe, _1712_b), _1712_b, _1709_toTpe), selfIdent, env, expectedOwnership, out _out249, out _out250, out _out251);
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
      DAST._IExpression _1735_expr = _let_tmp_rhs59.dtor_value;
      DAST._IType _1736_fromTpe = _let_tmp_rhs59.dtor_from;
      DAST._IType _1737_toTpe = _let_tmp_rhs59.dtor_typ;
      DAST._IType _let_tmp_rhs60 = _1736_fromTpe;
      DAST._IResolvedType _let_tmp_rhs61 = _let_tmp_rhs60.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1738___v122 = _let_tmp_rhs61.dtor_path;
      Dafny.ISequence<DAST._IType> _1739___v123 = _let_tmp_rhs61.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs62 = _let_tmp_rhs61.dtor_kind;
      DAST._IType _1740_b = _let_tmp_rhs62.dtor_baseType;
      DAST._INewtypeRange _1741_range = _let_tmp_rhs62.dtor_range;
      bool _1742_erase = _let_tmp_rhs62.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1743_attributes = _let_tmp_rhs61.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1744___v124 = _let_tmp_rhs61.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1745___v125 = _let_tmp_rhs61.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1746_nativeFromType;
      _1746_nativeFromType = DCOMP.COMP.NewtypeRangeToRustType(_1741_range);
      if (object.Equals(_1740_b, _1737_toTpe)) {
        RAST._IExpr _1747_recursiveGen;
        DCOMP._IOwnership _1748_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1749_recIdents;
        RAST._IExpr _out252;
        DCOMP._IOwnership _out253;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out254;
        (this).GenExpr(_1735_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out252, out _out253, out _out254);
        _1747_recursiveGen = _out252;
        _1748_recOwned = _out253;
        _1749_recIdents = _out254;
        readIdents = _1749_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source93 = _1746_nativeFromType;
        bool unmatched93 = true;
        if (unmatched93) {
          if (_source93.is_Some) {
            RAST._IType _1750_v = _source93.dtor_value;
            unmatched93 = false;
            RAST._IType _1751_toTpeRust;
            RAST._IType _out255;
            _out255 = (this).GenType(_1737_toTpe, DCOMP.GenTypeContext.@default());
            _1751_toTpeRust = _out255;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1751_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1747_recursiveGen));
            RAST._IExpr _out256;
            DCOMP._IOwnership _out257;
            (this).FromOwned(r, expectedOwnership, out _out256, out _out257);
            r = _out256;
            resultingOwnership = _out257;
          }
        }
        if (unmatched93) {
          unmatched93 = false;
          if (_1742_erase) {
            r = _1747_recursiveGen;
          } else {
            r = (_1747_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out258;
          DCOMP._IOwnership _out259;
          (this).FromOwnership(r, _1748_recOwned, expectedOwnership, out _out258, out _out259);
          r = _out258;
          resultingOwnership = _out259;
        }
      } else {
        if ((_1746_nativeFromType).is_Some) {
          if (object.Equals(_1737_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1752_recursiveGen;
            DCOMP._IOwnership _1753_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1754_recIdents;
            RAST._IExpr _out260;
            DCOMP._IOwnership _out261;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
            (this).GenExpr(_1735_expr, selfIdent, env, expectedOwnership, out _out260, out _out261, out _out262);
            _1752_recursiveGen = _out260;
            _1753_recOwned = _out261;
            _1754_recIdents = _out262;
            RAST._IExpr _out263;
            DCOMP._IOwnership _out264;
            (this).FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1752_recursiveGen, (this).DafnyCharUnderlying)), _1753_recOwned, expectedOwnership, out _out263, out _out264);
            r = _out263;
            resultingOwnership = _out264;
            readIdents = _1754_recIdents;
            return ;
          }
        }
        RAST._IExpr _out265;
        DCOMP._IOwnership _out266;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out267;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1735_expr, _1736_fromTpe, _1740_b), _1740_b, _1737_toTpe), selfIdent, env, expectedOwnership, out _out265, out _out266, out _out267);
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
        Std.Wrappers._IResult<__T, __E> _1755_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1755_valueOrError0).IsFailure()) {
          return (_1755_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1756_head = (_1755_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1757_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1757_valueOrError1).IsFailure()) {
            return (_1757_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1758_tail = (_1757_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1756_head), _1758_tail));
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
          RAST._IType _1759_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1760_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel((this).upcast)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1759_fromTpeUnderlying, _1760_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1761_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1761_valueOrError0).IsFailure()) {
          return (_1761_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1762_lambda = (_1761_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1762_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).Apply1(_1762_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1763_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim12 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr12 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
          for (int i12 = 0; i12 < dim12; i12++) {
            var _1764_i = (BigInteger) i12;
            arr12[(int)(_1764_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_1764_i), ((fromTpe).dtor_arguments).Select(_1764_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_1764_i), ((toTpe).dtor_arguments).Select(_1764_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr12);
        }))());
        if ((_1763_valueOrError1).IsFailure()) {
          return (_1763_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1765_lambdas = (_1763_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim13 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr13 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
  for (int i13 = 0; i13 < dim13; i13++) {
    var _1766_i = (BigInteger) i13;
    arr13[(int)(_1766_i)] = ((fromTpe).dtor_arguments).Select(_1766_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr13);
}))())).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1765_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1767_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1768_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1769_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1770_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1771_valueOrError2 = (this).UpcastConversionLambda(_1769_newFromType, _1767_newFromTpe, _1770_newToType, _1768_newToTpe, typeParams);
        if ((_1771_valueOrError2).IsFailure()) {
          return (_1771_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1772_coerceArg = (_1771_valueOrError2).Extract();
          RAST._IExpr _1773_collectionType = (RAST.__default.dafny__runtime).MSel((((fromTpe).Expand()).dtor_baseName).dtor_name);
          RAST._IExpr _1774_baseType = ((((((fromTpe).Expand()).dtor_baseName).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? ((_1773_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((((fromTpe).Expand()).dtor_arguments).Select(BigInteger.Zero), _1767_newFromTpe))) : ((_1773_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1767_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1774_baseType).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1772_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1775_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1775_valueOrError3).IsFailure()) {
          return (_1775_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1776_lambda = (_1775_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1776_lambda));
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
      DAST._IExpression _1777_expr = _let_tmp_rhs63.dtor_value;
      DAST._IType _1778_fromTpe = _let_tmp_rhs63.dtor_from;
      DAST._IType _1779_toTpe = _let_tmp_rhs63.dtor_typ;
      RAST._IType _1780_fromTpeGen;
      RAST._IType _out268;
      _out268 = (this).GenType(_1778_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1780_fromTpeGen = _out268;
      RAST._IType _1781_toTpeGen;
      RAST._IType _out269;
      _out269 = (this).GenType(_1779_toTpe, DCOMP.GenTypeContext.InBinding());
      _1781_toTpeGen = _out269;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1782_upcastConverter;
      _1782_upcastConverter = (this).UpcastConversionLambda(_1778_fromTpe, _1780_fromTpeGen, _1779_toTpe, _1781_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1782_upcastConverter).is_Success) {
        RAST._IExpr _1783_conversionLambda;
        _1783_conversionLambda = (_1782_upcastConverter).dtor_value;
        RAST._IExpr _1784_recursiveGen;
        DCOMP._IOwnership _1785_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1786_recIdents;
        RAST._IExpr _out270;
        DCOMP._IOwnership _out271;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out272;
        (this).GenExpr(_1777_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out270, out _out271, out _out272);
        _1784_recursiveGen = _out270;
        _1785_recOwned = _out271;
        _1786_recIdents = _out272;
        readIdents = _1786_recIdents;
        r = (_1783_conversionLambda).Apply1(_1784_recursiveGen);
        RAST._IExpr _out273;
        DCOMP._IOwnership _out274;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out273, out _out274);
        r = _out273;
        resultingOwnership = _out274;
      } else if ((this).IsDowncastConversion(_1780_fromTpeGen, _1781_toTpeGen)) {
        RAST._IExpr _1787_recursiveGen;
        DCOMP._IOwnership _1788_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1789_recIdents;
        RAST._IExpr _out275;
        DCOMP._IOwnership _out276;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out277;
        (this).GenExpr(_1777_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out275, out _out276, out _out277);
        _1787_recursiveGen = _out275;
        _1788_recOwned = _out276;
        _1789_recIdents = _out277;
        readIdents = _1789_recIdents;
        _1781_toTpeGen = (_1781_toTpeGen).ObjectOrPointerUnderlying();
        r = ((RAST.__default.dafny__runtime).MSel((this).downcast)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1787_recursiveGen, RAST.Expr.create_ExprFromType(_1781_toTpeGen)));
        RAST._IExpr _out278;
        DCOMP._IOwnership _out279;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out278, out _out279);
        r = _out278;
        resultingOwnership = _out279;
      } else {
        RAST._IExpr _1790_recursiveGen;
        DCOMP._IOwnership _1791_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1792_recIdents;
        RAST._IExpr _out280;
        DCOMP._IOwnership _out281;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out282;
        (this).GenExpr(_1777_expr, selfIdent, env, expectedOwnership, out _out280, out _out281, out _out282);
        _1790_recursiveGen = _out280;
        _1791_recOwned = _out281;
        _1792_recIdents = _out282;
        readIdents = _1792_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs64 = _1782_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs65 = _let_tmp_rhs64.dtor_error;
        DAST._IType _1793_fromType = _let_tmp_rhs65.dtor__0;
        RAST._IType _1794_fromTpeGen = _let_tmp_rhs65.dtor__1;
        DAST._IType _1795_toType = _let_tmp_rhs65.dtor__2;
        RAST._IType _1796_toTpeGen = _let_tmp_rhs65.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1797_m = _let_tmp_rhs65.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1798_msg;
        _1798_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1794_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1796_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1798_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1790_recursiveGen)._ToString(DCOMP.__default.IND), _1798_msg));
        RAST._IExpr _out283;
        DCOMP._IOwnership _out284;
        (this).FromOwnership(r, _1791_recOwned, expectedOwnership, out _out283, out _out284);
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
      DAST._IExpression _1799_expr = _let_tmp_rhs66.dtor_value;
      DAST._IType _1800_fromTpe = _let_tmp_rhs66.dtor_from;
      DAST._IType _1801_toTpe = _let_tmp_rhs66.dtor_typ;
      if (object.Equals(_1800_fromTpe, _1801_toTpe)) {
        RAST._IExpr _1802_recursiveGen;
        DCOMP._IOwnership _1803_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1804_recIdents;
        RAST._IExpr _out285;
        DCOMP._IOwnership _out286;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out287;
        (this).GenExpr(_1799_expr, selfIdent, env, expectedOwnership, out _out285, out _out286, out _out287);
        _1802_recursiveGen = _out285;
        _1803_recOwned = _out286;
        _1804_recIdents = _out287;
        r = _1802_recursiveGen;
        RAST._IExpr _out288;
        DCOMP._IOwnership _out289;
        (this).FromOwnership(r, _1803_recOwned, expectedOwnership, out _out288, out _out289);
        r = _out288;
        resultingOwnership = _out289;
        readIdents = _1804_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source94 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1800_fromTpe, _1801_toTpe);
        bool unmatched94 = true;
        if (unmatched94) {
          DAST._IType _10 = _source94.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1805_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1806_range = kind2.dtor_range;
              bool _1807_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1808_attributes = resolved2.dtor_attributes;
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
              DAST._IType _1809_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1810_range = kind3.dtor_range;
              bool _1811_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1812_attributes = resolved3.dtor_attributes;
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
                    RAST._IExpr _1813_recursiveGen;
                    DCOMP._IOwnership _1814___v136;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1815_recIdents;
                    RAST._IExpr _out296;
                    DCOMP._IOwnership _out297;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out298;
                    (this).GenExpr(_1799_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out296, out _out297, out _out298);
                    _1813_recursiveGen = _out296;
                    _1814___v136 = _out297;
                    _1815_recIdents = _out298;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1813_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out299;
                    DCOMP._IOwnership _out300;
                    (this).FromOwned(r, expectedOwnership, out _out299, out _out300);
                    r = _out299;
                    resultingOwnership = _out300;
                    readIdents = _1815_recIdents;
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
                    RAST._IExpr _1816_recursiveGen;
                    DCOMP._IOwnership _1817___v137;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1818_recIdents;
                    RAST._IExpr _out301;
                    DCOMP._IOwnership _out302;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out303;
                    (this).GenExpr(_1799_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out301, out _out302, out _out303);
                    _1816_recursiveGen = _out301;
                    _1817___v137 = _out302;
                    _1818_recIdents = _out303;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1816_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out304;
                    DCOMP._IOwnership _out305;
                    (this).FromOwned(r, expectedOwnership, out _out304, out _out305);
                    r = _out304;
                    resultingOwnership = _out305;
                    readIdents = _1818_recIdents;
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
                  RAST._IType _1819_rhsType;
                  RAST._IType _out306;
                  _out306 = (this).GenType(_1801_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1819_rhsType = _out306;
                  RAST._IExpr _1820_recursiveGen;
                  DCOMP._IOwnership _1821___v139;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1822_recIdents;
                  RAST._IExpr _out307;
                  DCOMP._IOwnership _out308;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out309;
                  (this).GenExpr(_1799_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out307, out _out308, out _out309);
                  _1820_recursiveGen = _out307;
                  _1821___v139 = _out308;
                  _1822_recIdents = _out309;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1819_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1820_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out310;
                  DCOMP._IOwnership _out311;
                  (this).FromOwned(r, expectedOwnership, out _out310, out _out311);
                  r = _out310;
                  resultingOwnership = _out311;
                  readIdents = _1822_recIdents;
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
                  RAST._IType _1823_rhsType;
                  RAST._IType _out312;
                  _out312 = (this).GenType(_1800_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1823_rhsType = _out312;
                  RAST._IExpr _1824_recursiveGen;
                  DCOMP._IOwnership _1825___v141;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1826_recIdents;
                  RAST._IExpr _out313;
                  DCOMP._IOwnership _out314;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out315;
                  (this).GenExpr(_1799_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out313, out _out314, out _out315);
                  _1824_recursiveGen = _out313;
                  _1825___v141 = _out314;
                  _1826_recIdents = _out315;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1824_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out316;
                  DCOMP._IOwnership _out317;
                  (this).FromOwned(r, expectedOwnership, out _out316, out _out317);
                  r = _out316;
                  resultingOwnership = _out317;
                  readIdents = _1826_recIdents;
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
                    RAST._IType _1827_rhsType;
                    RAST._IType _out318;
                    _out318 = (this).GenType(_1801_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1827_rhsType = _out318;
                    RAST._IExpr _1828_recursiveGen;
                    DCOMP._IOwnership _1829___v142;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1830_recIdents;
                    RAST._IExpr _out319;
                    DCOMP._IOwnership _out320;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out321;
                    (this).GenExpr(_1799_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out319, out _out320, out _out321);
                    _1828_recursiveGen = _out319;
                    _1829___v142 = _out320;
                    _1830_recIdents = _out321;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1828_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out322;
                    DCOMP._IOwnership _out323;
                    (this).FromOwned(r, expectedOwnership, out _out322, out _out323);
                    r = _out322;
                    resultingOwnership = _out323;
                    readIdents = _1830_recIdents;
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
                    RAST._IType _1831_rhsType;
                    RAST._IType _out324;
                    _out324 = (this).GenType(_1800_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1831_rhsType = _out324;
                    RAST._IExpr _1832_recursiveGen;
                    DCOMP._IOwnership _1833___v143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1834_recIdents;
                    RAST._IExpr _out325;
                    DCOMP._IOwnership _out326;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out327;
                    (this).GenExpr(_1799_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out325, out _out326, out _out327);
                    _1832_recursiveGen = _out325;
                    _1833___v143 = _out326;
                    _1834_recIdents = _out327;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1832_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out328;
                    DCOMP._IOwnership _out329;
                    (this).FromOwned(r, expectedOwnership, out _out328, out _out329);
                    r = _out328;
                    resultingOwnership = _out329;
                    readIdents = _1834_recIdents;
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
                RAST._IExpr _1835_recursiveGen;
                DCOMP._IOwnership _1836___v146;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1837_recIdents;
                RAST._IExpr _out330;
                DCOMP._IOwnership _out331;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out332;
                (this).GenExpr(_1799_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out330, out _out331, out _out332);
                _1835_recursiveGen = _out330;
                _1836___v146 = _out331;
                _1837_recIdents = _out332;
                RAST._IType _1838_toTpeGen;
                RAST._IType _out333;
                _out333 = (this).GenType(_1801_toTpe, DCOMP.GenTypeContext.InBinding());
                _1838_toTpeGen = _out333;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1835_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1838_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out334;
                DCOMP._IOwnership _out335;
                (this).FromOwned(r, expectedOwnership, out _out334, out _out335);
                r = _out334;
                resultingOwnership = _out335;
                readIdents = _1837_recIdents;
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
      Std.Wrappers._IOption<RAST._IType> _1839_tpe;
      _1839_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1840_placeboOpt;
      _1840_placeboOpt = (((_1839_tpe).is_Some) ? (((_1839_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1841_currentlyBorrowed;
      _1841_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1842_noNeedOfClone;
      _1842_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1840_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1841_currentlyBorrowed = false;
        _1842_noNeedOfClone = true;
        _1839_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1840_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_1841_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1839_tpe).is_Some) && (((_1839_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1843_needObjectFromRef;
        _1843_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source95 = (selfIdent).dtor_dafnyType;
          bool unmatched95 = true;
          if (unmatched95) {
            if (_source95.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source95.dtor_resolved;
              DAST._IResolvedTypeBase _1844_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1845_attributes = resolved4.dtor_attributes;
              unmatched95 = false;
              return ((_1844_base).is_Class) || ((_1844_base).is_Trait);
            }
          }
          if (unmatched95) {
            unmatched95 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_1843_needObjectFromRef) {
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1842_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1842_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1841_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1839_tpe).is_Some) && (((_1839_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1846_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1846_attributes).UniqueElements, false, (((_exists_var_1) => {
        DAST._IAttribute _1847_attribute = (DAST._IAttribute)_exists_var_1;
        return ((_1846_attributes).Contains(_1847_attribute)) && ((((_1847_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1847_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      Dafny.ISequence<DAST._IFormal> _1848_signature;
      _1848_signature = (((name).is_CallName) ? ((((((name).dtor_receiverArg).is_Some) && ((name).dtor_receiverAsArgument)) ? (Dafny.Sequence<DAST._IFormal>.Concat(Dafny.Sequence<DAST._IFormal>.FromElements(((name).dtor_receiverArg).dtor_value), ((name).dtor_signature))) : (((name).dtor_signature)))) : (Dafny.Sequence<DAST._IFormal>.FromElements()));
      BigInteger _hi38 = new BigInteger((args).Count);
      for (BigInteger _1849_i = BigInteger.Zero; _1849_i < _hi38; _1849_i++) {
        DCOMP._IOwnership _1850_argOwnership;
        _1850_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if ((_1849_i) < (new BigInteger((_1848_signature).Count))) {
          RAST._IType _1851_tpe;
          RAST._IType _out339;
          _out339 = (this).GenType(((_1848_signature).Select(_1849_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1851_tpe = _out339;
          if ((_1851_tpe).CanReadWithoutClone()) {
            _1850_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1852_argExpr;
        DCOMP._IOwnership _1853___v153;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1854_argIdents;
        RAST._IExpr _out340;
        DCOMP._IOwnership _out341;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out342;
        (this).GenExpr((args).Select(_1849_i), selfIdent, env, _1850_argOwnership, out _out340, out _out341, out _out342);
        _1852_argExpr = _out340;
        _1853___v153 = _out341;
        _1854_argIdents = _out342;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1852_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1854_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi39 = new BigInteger((typeArgs).Count);
      for (BigInteger _1855_typeI = BigInteger.Zero; _1855_typeI < _hi39; _1855_typeI++) {
        RAST._IType _1856_typeExpr;
        RAST._IType _out343;
        _out343 = (this).GenType((typeArgs).Select(_1855_typeI), DCOMP.GenTypeContext.@default());
        _1856_typeExpr = _out343;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1856_typeExpr));
      }
      DAST._ICallName _source96 = name;
      bool unmatched96 = true;
      if (unmatched96) {
        if (_source96.is_CallName) {
          Dafny.ISequence<Dafny.Rune> _1857_nameIdent = _source96.dtor_name;
          Std.Wrappers._IOption<DAST._IType> onType1 = _source96.dtor_onType;
          if (onType1.is_Some) {
            DAST._IType value10 = onType1.dtor_value;
            if (value10.is_UserDefined) {
              DAST._IResolvedType _1858_resolvedType = value10.dtor_resolved;
              unmatched96 = false;
              if ((((_1858_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_1859_resolvedType, _1860_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(Dafny.Helpers.SingleValue<Dafny.ISequence<Dafny.Rune>>(_1860_nameIdent), true, (((_forall_var_8) => {
                Dafny.ISequence<Dafny.Rune> _1861_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                return !(((_1859_resolvedType).dtor_properMethods).Contains(_1861_m)) || (!object.Equals(_1861_m, _1860_nameIdent));
              }))))(_1858_resolvedType, _1857_nameIdent))) {
                fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_1858_resolvedType, (_1857_nameIdent)), _1858_resolvedType));
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
          Dafny.ISequence<Dafny.Rune> _1862_ident = _source97.dtor_name;
          unmatched97 = false;
          if ((_pat_let_tv146).is_ExternCompanion) {
            return (_1862_ident);
          } else {
            return DCOMP.__default.escapeName(_1862_ident);
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
          Dafny.ISequence<Dafny.Rune> _1863_name = _source98.dtor_name;
          unmatched98 = false;
          {
            RAST._IExpr _out347;
            DCOMP._IOwnership _out348;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
            (this).GenIdent(DCOMP.__default.escapeVar(_1863_name), selfIdent, env, expectedOwnership, out _out347, out _out348, out _out349);
            r = _out347;
            resultingOwnership = _out348;
            readIdents = _out349;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_ExternCompanion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1864_path = _source98.dtor_ExternCompanion_a0;
          unmatched98 = false;
          {
            RAST._IExpr _out350;
            _out350 = DCOMP.COMP.GenPathExpr(_1864_path, false);
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
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1865_path = _source98.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _1866_typeArgs = _source98.dtor_typeArgs;
          unmatched98 = false;
          {
            RAST._IExpr _out353;
            _out353 = DCOMP.COMP.GenPathExpr(_1865_path, true);
            r = _out353;
            if ((new BigInteger((_1866_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1867_typeExprs;
              _1867_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_1866_typeArgs).Count);
              for (BigInteger _1868_i = BigInteger.Zero; _1868_i < _hi40; _1868_i++) {
                RAST._IType _1869_typeExpr;
                RAST._IType _out354;
                _out354 = (this).GenType((_1866_typeArgs).Select(_1868_i), DCOMP.GenTypeContext.@default());
                _1869_typeExpr = _out354;
                _1867_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1867_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1869_typeExpr));
              }
              r = (r).ApplyType(_1867_typeExprs);
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
          DAST._IType _1870_typ = _source98.dtor_typ;
          unmatched98 = false;
          {
            RAST._IType _1871_typExpr;
            RAST._IType _out357;
            _out357 = (this).GenType(_1870_typ, DCOMP.GenTypeContext.@default());
            _1871_typExpr = _out357;
            if ((_1871_typExpr).IsObjectOrPointer()) {
              r = (_1871_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1871_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
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
          Dafny.ISequence<DAST._IExpression> _1872_values = _source98.dtor_Tuple_a0;
          unmatched98 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1873_exprs;
            _1873_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi41 = new BigInteger((_1872_values).Count);
            for (BigInteger _1874_i = BigInteger.Zero; _1874_i < _hi41; _1874_i++) {
              RAST._IExpr _1875_recursiveGen;
              DCOMP._IOwnership _1876___v163;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1877_recIdents;
              RAST._IExpr _out360;
              DCOMP._IOwnership _out361;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out362;
              (this).GenExpr((_1872_values).Select(_1874_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out360, out _out361, out _out362);
              _1875_recursiveGen = _out360;
              _1876___v163 = _out361;
              _1877_recIdents = _out362;
              _1873_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1873_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1875_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1877_recIdents);
            }
            r = (((new BigInteger((_1872_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1873_exprs)) : (RAST.__default.SystemTuple(_1873_exprs)));
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
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1878_path = _source98.dtor_path;
          Dafny.ISequence<DAST._IType> _1879_typeArgs = _source98.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1880_args = _source98.dtor_args;
          unmatched98 = false;
          {
            RAST._IExpr _out365;
            _out365 = DCOMP.COMP.GenPathExpr(_1878_path, true);
            r = _out365;
            if ((new BigInteger((_1879_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1881_typeExprs;
              _1881_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi42 = new BigInteger((_1879_typeArgs).Count);
              for (BigInteger _1882_i = BigInteger.Zero; _1882_i < _hi42; _1882_i++) {
                RAST._IType _1883_typeExpr;
                RAST._IType _out366;
                _out366 = (this).GenType((_1879_typeArgs).Select(_1882_i), DCOMP.GenTypeContext.@default());
                _1883_typeExpr = _out366;
                _1881_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1881_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1883_typeExpr));
              }
              r = (r).ApplyType(_1881_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1884_arguments;
            _1884_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi43 = new BigInteger((_1880_args).Count);
            for (BigInteger _1885_i = BigInteger.Zero; _1885_i < _hi43; _1885_i++) {
              RAST._IExpr _1886_recursiveGen;
              DCOMP._IOwnership _1887___v164;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1888_recIdents;
              RAST._IExpr _out367;
              DCOMP._IOwnership _out368;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out369;
              (this).GenExpr((_1880_args).Select(_1885_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out367, out _out368, out _out369);
              _1886_recursiveGen = _out367;
              _1887___v164 = _out368;
              _1888_recIdents = _out369;
              _1884_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1884_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1886_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1888_recIdents);
            }
            r = (r).Apply(_1884_arguments);
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
          Dafny.ISequence<DAST._IExpression> _1889_dims = _source98.dtor_dims;
          DAST._IType _1890_typ = _source98.dtor_typ;
          unmatched98 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1889_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1891_msg;
              _1891_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1891_msg);
              }
              r = RAST.Expr.create_RawExpr(_1891_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1892_typeGen;
              RAST._IType _out372;
              _out372 = (this).GenType(_1890_typ, DCOMP.GenTypeContext.@default());
              _1892_typeGen = _out372;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1893_dimExprs;
              _1893_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi44 = new BigInteger((_1889_dims).Count);
              for (BigInteger _1894_i = BigInteger.Zero; _1894_i < _hi44; _1894_i++) {
                RAST._IExpr _1895_recursiveGen;
                DCOMP._IOwnership _1896___v165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1897_recIdents;
                RAST._IExpr _out373;
                DCOMP._IOwnership _out374;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out375;
                (this).GenExpr((_1889_dims).Select(_1894_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out373, out _out374, out _out375);
                _1895_recursiveGen = _out373;
                _1896___v165 = _out374;
                _1897_recIdents = _out375;
                _1893_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1893_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.IntoUsize(_1895_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1897_recIdents);
              }
              if ((new BigInteger((_1889_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1898_class__name;
                _1898_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1889_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1898_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1892_typeGen))).MSel((this).placebos__usize)).Apply(_1893_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1892_typeGen))).Apply(_1893_dimExprs);
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
          DAST._IExpression _1899_underlying = _source98.dtor_value;
          unmatched98 = false;
          {
            RAST._IExpr _1900_recursiveGen;
            DCOMP._IOwnership _1901___v166;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1902_recIdents;
            RAST._IExpr _out378;
            DCOMP._IOwnership _out379;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out380;
            (this).GenExpr(_1899_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out378, out _out379, out _out380);
            _1900_recursiveGen = _out378;
            _1901___v166 = _out379;
            _1902_recIdents = _out380;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1900_recursiveGen);
            readIdents = _1902_recIdents;
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
          DAST._IExpression _1903_underlying = _source98.dtor_value;
          DAST._IType _1904_typ = _source98.dtor_typ;
          unmatched98 = false;
          {
            RAST._IType _1905_tpe;
            RAST._IType _out383;
            _out383 = (this).GenType(_1904_typ, DCOMP.GenTypeContext.@default());
            _1905_tpe = _out383;
            RAST._IExpr _1906_recursiveGen;
            DCOMP._IOwnership _1907___v167;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1908_recIdents;
            RAST._IExpr _out384;
            DCOMP._IOwnership _out385;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out386;
            (this).GenExpr(_1903_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out384, out _out385, out _out386);
            _1906_recursiveGen = _out384;
            _1907___v167 = _out385;
            _1908_recIdents = _out386;
            readIdents = _1908_recIdents;
            if ((_1905_tpe).IsObjectOrPointer()) {
              RAST._IType _1909_t;
              _1909_t = (_1905_tpe).ObjectOrPointerUnderlying();
              if ((_1909_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1906_recursiveGen);
              } else if ((_1909_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1910_c;
                _1910_c = (_1909_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1910_c)).MSel((this).array__construct)).Apply1(_1906_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1905_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1905_tpe)._ToString(DCOMP.__default.IND)));
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
          DAST._IResolvedType _1911_datatypeType = _source98.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1912_typeArgs = _source98.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1913_variant = _source98.dtor_variant;
          bool _1914_isCo = _source98.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1915_values = _source98.dtor_contents;
          unmatched98 = false;
          {
            RAST._IExpr _out389;
            _out389 = DCOMP.COMP.GenPathExpr((_1911_datatypeType).dtor_path, true);
            r = _out389;
            Dafny.ISequence<RAST._IType> _1916_genTypeArgs;
            _1916_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi45 = new BigInteger((_1912_typeArgs).Count);
            for (BigInteger _1917_i = BigInteger.Zero; _1917_i < _hi45; _1917_i++) {
              RAST._IType _1918_typeExpr;
              RAST._IType _out390;
              _out390 = (this).GenType((_1912_typeArgs).Select(_1917_i), DCOMP.GenTypeContext.@default());
              _1918_typeExpr = _out390;
              _1916_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1916_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1918_typeExpr));
            }
            if ((new BigInteger((_1912_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1916_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1913_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1919_assignments;
            _1919_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi46 = new BigInteger((_1915_values).Count);
            for (BigInteger _1920_i = BigInteger.Zero; _1920_i < _hi46; _1920_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs67 = (_1915_values).Select(_1920_i);
              Dafny.ISequence<Dafny.Rune> _1921_name = _let_tmp_rhs67.dtor__0;
              DAST._IExpression _1922_value = _let_tmp_rhs67.dtor__1;
              if (_1914_isCo) {
                RAST._IExpr _1923_recursiveGen;
                DCOMP._IOwnership _1924___v168;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1925_recIdents;
                RAST._IExpr _out391;
                DCOMP._IOwnership _out392;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out393;
                (this).GenExpr(_1922_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out391, out _out392, out _out393);
                _1923_recursiveGen = _out391;
                _1924___v168 = _out392;
                _1925_recIdents = _out393;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1925_recIdents);
                Dafny.ISequence<Dafny.Rune> _1926_allReadCloned;
                _1926_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1925_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1927_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1925_recIdents).Elements) {
                    _1927_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1925_recIdents).Contains(_1927_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4597)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1926_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1926_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1927_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1927_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1925_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1925_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1927_next));
                }
                Dafny.ISequence<Dafny.Rune> _1928_wasAssigned;
                _1928_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1926_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1923_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1919_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1919_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_1921_name), RAST.Expr.create_RawExpr(_1928_wasAssigned))));
              } else {
                RAST._IExpr _1929_recursiveGen;
                DCOMP._IOwnership _1930___v169;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1931_recIdents;
                RAST._IExpr _out394;
                DCOMP._IOwnership _out395;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out396;
                (this).GenExpr(_1922_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out394, out _out395, out _out396);
                _1929_recursiveGen = _out394;
                _1930___v169 = _out395;
                _1931_recIdents = _out396;
                _1919_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1919_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeVar(_1921_name), _1929_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1931_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1919_assignments);
            if ((this).IsRcWrapped((_1911_datatypeType).dtor_attributes)) {
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
          DAST._IExpression _1932_length = _source98.dtor_length;
          DAST._IExpression _1933_expr = _source98.dtor_elem;
          unmatched98 = false;
          {
            RAST._IExpr _1934_recursiveGen;
            DCOMP._IOwnership _1935___v173;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1936_recIdents;
            RAST._IExpr _out402;
            DCOMP._IOwnership _out403;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out404;
            (this).GenExpr(_1933_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out402, out _out403, out _out404);
            _1934_recursiveGen = _out402;
            _1935___v173 = _out403;
            _1936_recIdents = _out404;
            RAST._IExpr _1937_lengthGen;
            DCOMP._IOwnership _1938___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1939_lengthIdents;
            RAST._IExpr _out405;
            DCOMP._IOwnership _out406;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out407;
            (this).GenExpr(_1932_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out405, out _out406, out _out407);
            _1937_lengthGen = _out405;
            _1938___v174 = _out406;
            _1939_lengthIdents = _out407;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1934_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1937_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1936_recIdents, _1939_lengthIdents);
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
          Dafny.ISequence<DAST._IExpression> _1940_exprs = _source98.dtor_elements;
          DAST._IType _1941_typ = _source98.dtor_typ;
          unmatched98 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1942_genTpe;
            RAST._IType _out410;
            _out410 = (this).GenType(_1941_typ, DCOMP.GenTypeContext.@default());
            _1942_genTpe = _out410;
            BigInteger _1943_i;
            _1943_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1944_args;
            _1944_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1943_i) < (new BigInteger((_1940_exprs).Count))) {
              RAST._IExpr _1945_recursiveGen;
              DCOMP._IOwnership _1946___v175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1947_recIdents;
              RAST._IExpr _out411;
              DCOMP._IOwnership _out412;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out413;
              (this).GenExpr((_1940_exprs).Select(_1943_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out411, out _out412, out _out413);
              _1945_recursiveGen = _out411;
              _1946___v175 = _out412;
              _1947_recIdents = _out413;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1947_recIdents);
              _1944_args = Dafny.Sequence<RAST._IExpr>.Concat(_1944_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1945_recursiveGen));
              _1943_i = (_1943_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1944_args);
            if ((new BigInteger((_1944_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1942_genTpe));
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
          Dafny.ISequence<DAST._IExpression> _1948_exprs = _source98.dtor_elements;
          unmatched98 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1949_generatedValues;
            _1949_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1950_i;
            _1950_i = BigInteger.Zero;
            while ((_1950_i) < (new BigInteger((_1948_exprs).Count))) {
              RAST._IExpr _1951_recursiveGen;
              DCOMP._IOwnership _1952___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1953_recIdents;
              RAST._IExpr _out416;
              DCOMP._IOwnership _out417;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out418;
              (this).GenExpr((_1948_exprs).Select(_1950_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out416, out _out417, out _out418);
              _1951_recursiveGen = _out416;
              _1952___v176 = _out417;
              _1953_recIdents = _out418;
              _1949_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1949_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1951_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1953_recIdents);
              _1950_i = (_1950_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1949_generatedValues);
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
          Dafny.ISequence<DAST._IExpression> _1954_exprs = _source98.dtor_elements;
          unmatched98 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1955_generatedValues;
            _1955_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1956_i;
            _1956_i = BigInteger.Zero;
            while ((_1956_i) < (new BigInteger((_1954_exprs).Count))) {
              RAST._IExpr _1957_recursiveGen;
              DCOMP._IOwnership _1958___v177;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1959_recIdents;
              RAST._IExpr _out421;
              DCOMP._IOwnership _out422;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out423;
              (this).GenExpr((_1954_exprs).Select(_1956_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out421, out _out422, out _out423);
              _1957_recursiveGen = _out421;
              _1958___v177 = _out422;
              _1959_recIdents = _out423;
              _1955_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1955_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1957_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1959_recIdents);
              _1956_i = (_1956_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1955_generatedValues);
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
          DAST._IExpression _1960_expr = _source98.dtor_ToMultiset_a0;
          unmatched98 = false;
          {
            RAST._IExpr _1961_recursiveGen;
            DCOMP._IOwnership _1962___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1963_recIdents;
            RAST._IExpr _out426;
            DCOMP._IOwnership _out427;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out428;
            (this).GenExpr(_1960_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out426, out _out427, out _out428);
            _1961_recursiveGen = _out426;
            _1962___v178 = _out427;
            _1963_recIdents = _out428;
            r = ((_1961_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1963_recIdents;
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
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1964_mapElems = _source98.dtor_mapElems;
          unmatched98 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1965_generatedValues;
            _1965_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1966_i;
            _1966_i = BigInteger.Zero;
            while ((_1966_i) < (new BigInteger((_1964_mapElems).Count))) {
              RAST._IExpr _1967_recursiveGenKey;
              DCOMP._IOwnership _1968___v179;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1969_recIdentsKey;
              RAST._IExpr _out431;
              DCOMP._IOwnership _out432;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out433;
              (this).GenExpr(((_1964_mapElems).Select(_1966_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out431, out _out432, out _out433);
              _1967_recursiveGenKey = _out431;
              _1968___v179 = _out432;
              _1969_recIdentsKey = _out433;
              RAST._IExpr _1970_recursiveGenValue;
              DCOMP._IOwnership _1971___v180;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1972_recIdentsValue;
              RAST._IExpr _out434;
              DCOMP._IOwnership _out435;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out436;
              (this).GenExpr(((_1964_mapElems).Select(_1966_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out434, out _out435, out _out436);
              _1970_recursiveGenValue = _out434;
              _1971___v180 = _out435;
              _1972_recIdentsValue = _out436;
              _1965_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1965_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1967_recursiveGenKey, _1970_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1969_recIdentsKey), _1972_recIdentsValue);
              _1966_i = (_1966_i) + (BigInteger.One);
            }
            _1966_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1973_arguments;
            _1973_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1966_i) < (new BigInteger((_1965_generatedValues).Count))) {
              RAST._IExpr _1974_genKey;
              _1974_genKey = ((_1965_generatedValues).Select(_1966_i)).dtor__0;
              RAST._IExpr _1975_genValue;
              _1975_genValue = ((_1965_generatedValues).Select(_1966_i)).dtor__1;
              _1973_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1973_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1974_genKey, _1975_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1966_i = (_1966_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1973_arguments);
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
          DAST._IExpression _1976_expr = _source98.dtor_expr;
          DAST._IExpression _1977_index = _source98.dtor_indexExpr;
          DAST._IExpression _1978_value = _source98.dtor_value;
          unmatched98 = false;
          {
            RAST._IExpr _1979_exprR;
            DCOMP._IOwnership _1980___v181;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1981_exprIdents;
            RAST._IExpr _out439;
            DCOMP._IOwnership _out440;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out441;
            (this).GenExpr(_1976_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out439, out _out440, out _out441);
            _1979_exprR = _out439;
            _1980___v181 = _out440;
            _1981_exprIdents = _out441;
            RAST._IExpr _1982_indexR;
            DCOMP._IOwnership _1983_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1984_indexIdents;
            RAST._IExpr _out442;
            DCOMP._IOwnership _out443;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out444;
            (this).GenExpr(_1977_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out442, out _out443, out _out444);
            _1982_indexR = _out442;
            _1983_indexOwnership = _out443;
            _1984_indexIdents = _out444;
            RAST._IExpr _1985_valueR;
            DCOMP._IOwnership _1986_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1987_valueIdents;
            RAST._IExpr _out445;
            DCOMP._IOwnership _out446;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out447;
            (this).GenExpr(_1978_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out445, out _out446, out _out447);
            _1985_valueR = _out445;
            _1986_valueOwnership = _out446;
            _1987_valueIdents = _out447;
            r = ((_1979_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1982_indexR, _1985_valueR));
            RAST._IExpr _out448;
            DCOMP._IOwnership _out449;
            (this).FromOwned(r, expectedOwnership, out _out448, out _out449);
            r = _out448;
            resultingOwnership = _out449;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1981_exprIdents, _1984_indexIdents), _1987_valueIdents);
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_MapUpdate) {
          DAST._IExpression _1988_expr = _source98.dtor_expr;
          DAST._IExpression _1989_index = _source98.dtor_indexExpr;
          DAST._IExpression _1990_value = _source98.dtor_value;
          unmatched98 = false;
          {
            RAST._IExpr _1991_exprR;
            DCOMP._IOwnership _1992___v182;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1993_exprIdents;
            RAST._IExpr _out450;
            DCOMP._IOwnership _out451;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out452;
            (this).GenExpr(_1988_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out450, out _out451, out _out452);
            _1991_exprR = _out450;
            _1992___v182 = _out451;
            _1993_exprIdents = _out452;
            RAST._IExpr _1994_indexR;
            DCOMP._IOwnership _1995_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1996_indexIdents;
            RAST._IExpr _out453;
            DCOMP._IOwnership _out454;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out455;
            (this).GenExpr(_1989_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out453, out _out454, out _out455);
            _1994_indexR = _out453;
            _1995_indexOwnership = _out454;
            _1996_indexIdents = _out455;
            RAST._IExpr _1997_valueR;
            DCOMP._IOwnership _1998_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1999_valueIdents;
            RAST._IExpr _out456;
            DCOMP._IOwnership _out457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out458;
            (this).GenExpr(_1990_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out456, out _out457, out _out458);
            _1997_valueR = _out456;
            _1998_valueOwnership = _out457;
            _1999_valueIdents = _out458;
            r = ((_1991_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1994_indexR, _1997_valueR));
            RAST._IExpr _out459;
            DCOMP._IOwnership _out460;
            (this).FromOwned(r, expectedOwnership, out _out459, out _out460);
            r = _out459;
            resultingOwnership = _out460;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1993_exprIdents, _1996_indexIdents), _1999_valueIdents);
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
                Dafny.ISequence<Dafny.Rune> _2000_id = _source99.dtor_rSelfName;
                DAST._IType _2001_dafnyType = _source99.dtor_dafnyType;
                unmatched99 = false;
                {
                  RAST._IExpr _out461;
                  DCOMP._IOwnership _out462;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out463;
                  (this).GenIdent(_2000_id, selfIdent, env, expectedOwnership, out _out461, out _out462, out _out463);
                  r = _out461;
                  resultingOwnership = _out462;
                  readIdents = _out463;
                }
              }
            }
            if (unmatched99) {
              DCOMP._ISelfInfo _2002_None = _source99;
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
          DAST._IExpression _2003_cond = _source98.dtor_cond;
          DAST._IExpression _2004_t = _source98.dtor_thn;
          DAST._IExpression _2005_f = _source98.dtor_els;
          unmatched98 = false;
          {
            RAST._IExpr _2006_cond;
            DCOMP._IOwnership _2007___v183;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2008_recIdentsCond;
            RAST._IExpr _out466;
            DCOMP._IOwnership _out467;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out468;
            (this).GenExpr(_2003_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out466, out _out467, out _out468);
            _2006_cond = _out466;
            _2007___v183 = _out467;
            _2008_recIdentsCond = _out468;
            RAST._IExpr _2009_fExpr;
            DCOMP._IOwnership _2010_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2011_recIdentsF;
            RAST._IExpr _out469;
            DCOMP._IOwnership _out470;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out471;
            (this).GenExpr(_2005_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out469, out _out470, out _out471);
            _2009_fExpr = _out469;
            _2010_fOwned = _out470;
            _2011_recIdentsF = _out471;
            RAST._IExpr _2012_tExpr;
            DCOMP._IOwnership _2013___v184;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2014_recIdentsT;
            RAST._IExpr _out472;
            DCOMP._IOwnership _out473;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out474;
            (this).GenExpr(_2004_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out472, out _out473, out _out474);
            _2012_tExpr = _out472;
            _2013___v184 = _out473;
            _2014_recIdentsT = _out474;
            r = RAST.Expr.create_IfExpr(_2006_cond, _2012_tExpr, _2009_fExpr);
            RAST._IExpr _out475;
            DCOMP._IOwnership _out476;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out475, out _out476);
            r = _out475;
            resultingOwnership = _out476;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2008_recIdentsCond, _2014_recIdentsT), _2011_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source98.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _2015_e = _source98.dtor_expr;
            DAST.Format._IUnaryOpFormat _2016_format = _source98.dtor_format1;
            unmatched98 = false;
            {
              RAST._IExpr _2017_recursiveGen;
              DCOMP._IOwnership _2018___v185;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2019_recIdents;
              RAST._IExpr _out477;
              DCOMP._IOwnership _out478;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out479;
              (this).GenExpr(_2015_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out477, out _out478, out _out479);
              _2017_recursiveGen = _out477;
              _2018___v185 = _out478;
              _2019_recIdents = _out479;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _2017_recursiveGen, _2016_format);
              RAST._IExpr _out480;
              DCOMP._IOwnership _out481;
              (this).FromOwned(r, expectedOwnership, out _out480, out _out481);
              r = _out480;
              resultingOwnership = _out481;
              readIdents = _2019_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source98.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _2020_e = _source98.dtor_expr;
            DAST.Format._IUnaryOpFormat _2021_format = _source98.dtor_format1;
            unmatched98 = false;
            {
              RAST._IExpr _2022_recursiveGen;
              DCOMP._IOwnership _2023___v186;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2024_recIdents;
              RAST._IExpr _out482;
              DCOMP._IOwnership _out483;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
              (this).GenExpr(_2020_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out482, out _out483, out _out484);
              _2022_recursiveGen = _out482;
              _2023___v186 = _out483;
              _2024_recIdents = _out484;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _2022_recursiveGen, _2021_format);
              RAST._IExpr _out485;
              DCOMP._IOwnership _out486;
              (this).FromOwned(r, expectedOwnership, out _out485, out _out486);
              r = _out485;
              resultingOwnership = _out486;
              readIdents = _2024_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source98.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _2025_e = _source98.dtor_expr;
            DAST.Format._IUnaryOpFormat _2026_format = _source98.dtor_format1;
            unmatched98 = false;
            {
              RAST._IExpr _2027_recursiveGen;
              DCOMP._IOwnership _2028_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2029_recIdents;
              RAST._IExpr _out487;
              DCOMP._IOwnership _out488;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out489;
              (this).GenExpr(_2025_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out487, out _out488, out _out489);
              _2027_recursiveGen = _out487;
              _2028_recOwned = _out488;
              _2029_recIdents = _out489;
              r = ((_2027_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out490;
              DCOMP._IOwnership _out491;
              (this).FromOwned(r, expectedOwnership, out _out490, out _out491);
              r = _out490;
              resultingOwnership = _out491;
              readIdents = _2029_recIdents;
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
          DAST._IExpression _2030_expr = _source98.dtor_expr;
          DAST._IType _2031_exprType = _source98.dtor_exprType;
          BigInteger _2032_dim = _source98.dtor_dim;
          bool _2033_native = _source98.dtor_native;
          unmatched98 = false;
          {
            RAST._IExpr _2034_recursiveGen;
            DCOMP._IOwnership _2035___v191;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2036_recIdents;
            RAST._IExpr _out495;
            DCOMP._IOwnership _out496;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out497;
            (this).GenExpr(_2030_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out495, out _out496, out _out497);
            _2034_recursiveGen = _out495;
            _2035___v191 = _out496;
            _2036_recIdents = _out497;
            RAST._IType _2037_arrayType;
            RAST._IType _out498;
            _out498 = (this).GenType(_2031_exprType, DCOMP.GenTypeContext.@default());
            _2037_arrayType = _out498;
            if (!((_2037_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2038_msg;
              _2038_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2037_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2038_msg);
              r = RAST.Expr.create_RawExpr(_2038_msg);
            } else {
              RAST._IType _2039_underlying;
              _2039_underlying = (_2037_arrayType).ObjectOrPointerUnderlying();
              if (((_2032_dim).Sign == 0) && ((_2039_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2034_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2032_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2034_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = ((((this).read__macro).Apply1(_2034_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("length"), Std.Strings.__default.OfNat(_2032_dim)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_usize")))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                }
              }
              if (!(_2033_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out499;
            DCOMP._IOwnership _out500;
            (this).FromOwned(r, expectedOwnership, out _out499, out _out500);
            r = _out499;
            resultingOwnership = _out500;
            readIdents = _2036_recIdents;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_MapKeys) {
          DAST._IExpression _2040_expr = _source98.dtor_expr;
          unmatched98 = false;
          {
            RAST._IExpr _2041_recursiveGen;
            DCOMP._IOwnership _2042___v192;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2043_recIdents;
            RAST._IExpr _out501;
            DCOMP._IOwnership _out502;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out503;
            (this).GenExpr(_2040_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out501, out _out502, out _out503);
            _2041_recursiveGen = _out501;
            _2042___v192 = _out502;
            _2043_recIdents = _out503;
            readIdents = _2043_recIdents;
            r = ((_2041_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _2044_expr = _source98.dtor_expr;
          unmatched98 = false;
          {
            RAST._IExpr _2045_recursiveGen;
            DCOMP._IOwnership _2046___v193;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2047_recIdents;
            RAST._IExpr _out506;
            DCOMP._IOwnership _out507;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out508;
            (this).GenExpr(_2044_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out506, out _out507, out _out508);
            _2045_recursiveGen = _out506;
            _2046___v193 = _out507;
            _2047_recIdents = _out508;
            readIdents = _2047_recIdents;
            r = ((_2045_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _2048_expr = _source98.dtor_expr;
          unmatched98 = false;
          {
            RAST._IExpr _2049_recursiveGen;
            DCOMP._IOwnership _2050___v194;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2051_recIdents;
            RAST._IExpr _out511;
            DCOMP._IOwnership _out512;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out513;
            (this).GenExpr(_2048_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out511, out _out512, out _out513);
            _2049_recursiveGen = _out511;
            _2050___v194 = _out512;
            _2051_recIdents = _out513;
            readIdents = _2051_recIdents;
            r = ((_2049_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("items"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _2052_on = _source98.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2053_field = _source98.dtor_field;
          bool _2054_isDatatype = _source98.dtor_onDatatype;
          bool _2055_isStatic = _source98.dtor_isStatic;
          bool _2056_isConstant = _source98.dtor_isConstant;
          Dafny.ISequence<DAST._IType> _2057_arguments = _source98.dtor_arguments;
          unmatched98 = false;
          {
            RAST._IExpr _2058_onExpr;
            DCOMP._IOwnership _2059_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2060_recIdents;
            RAST._IExpr _out516;
            DCOMP._IOwnership _out517;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out518;
            (this).GenExpr(_2052_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out516, out _out517, out _out518);
            _2058_onExpr = _out516;
            _2059_onOwned = _out517;
            _2060_recIdents = _out518;
            Dafny.ISequence<Dafny.Rune> _2061_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2062_onString;
            _2062_onString = (_2058_onExpr)._ToString(DCOMP.__default.IND);
            if (_2055_isStatic) {
              DCOMP._IEnvironment _2063_lEnv;
              _2063_lEnv = env;
              Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>> _2064_args;
              _2064_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements();
              _2061_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|");
              BigInteger _hi47 = new BigInteger((_2057_arguments).Count);
              for (BigInteger _2065_i = BigInteger.Zero; _2065_i < _hi47; _2065_i++) {
                if ((_2065_i).Sign == 1) {
                  _2061_s = Dafny.Sequence<Dafny.Rune>.Concat(_2061_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                RAST._IType _2066_ty;
                RAST._IType _out519;
                _out519 = (this).GenType((_2057_arguments).Select(_2065_i), DCOMP.GenTypeContext.@default());
                _2066_ty = _out519;
                RAST._IType _2067_bTy;
                _2067_bTy = RAST.Type.create_Borrowed(_2066_ty);
                Dafny.ISequence<Dafny.Rune> _2068_name;
                _2068_name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("x"), Std.Strings.__default.OfInt(_2065_i));
                _2063_lEnv = (_2063_lEnv).AddAssigned(_2068_name, _2067_bTy);
                _2064_args = Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.Concat(_2064_args, Dafny.Sequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>>.FromElements(_System.Tuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType>.create(_2068_name, _2066_ty)));
                _2061_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2061_s, _2068_name), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")), (_2067_bTy)._ToString(DCOMP.__default.IND));
              }
              _2061_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2061_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| ")), _2062_onString), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeVar(_2053_field)), ((_2056_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("));
              BigInteger _hi48 = new BigInteger((_2064_args).Count);
              for (BigInteger _2069_i = BigInteger.Zero; _2069_i < _hi48; _2069_i++) {
                if ((_2069_i).Sign == 1) {
                  _2061_s = Dafny.Sequence<Dafny.Rune>.Concat(_2061_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _System._ITuple2<Dafny.ISequence<Dafny.Rune>, RAST._IType> _let_tmp_rhs68 = (_2064_args).Select(_2069_i);
                Dafny.ISequence<Dafny.Rune> _2070_name = _let_tmp_rhs68.dtor__0;
                RAST._IType _2071_ty = _let_tmp_rhs68.dtor__1;
                RAST._IExpr _2072_rIdent;
                DCOMP._IOwnership _2073___v195;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2074___v196;
                RAST._IExpr _out520;
                DCOMP._IOwnership _out521;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out522;
                (this).GenIdent(_2070_name, selfIdent, _2063_lEnv, (((_2071_ty).CanReadWithoutClone()) ? (DCOMP.Ownership.create_OwnershipOwned()) : (DCOMP.Ownership.create_OwnershipBorrowed())), out _out520, out _out521, out _out522);
                _2072_rIdent = _out520;
                _2073___v195 = _out521;
                _2074___v196 = _out522;
                _2061_s = Dafny.Sequence<Dafny.Rune>.Concat(_2061_s, (_2072_rIdent)._ToString(DCOMP.__default.IND));
              }
              _2061_s = Dafny.Sequence<Dafny.Rune>.Concat(_2061_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
            } else {
              _2061_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2061_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2061_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2062_onString), ((object.Equals(_2059_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2075_args;
              _2075_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2076_i;
              _2076_i = BigInteger.Zero;
              while ((_2076_i) < (new BigInteger((_2057_arguments).Count))) {
                if ((_2076_i).Sign == 1) {
                  _2075_args = Dafny.Sequence<Dafny.Rune>.Concat(_2075_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2075_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2075_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2076_i));
                _2076_i = (_2076_i) + (BigInteger.One);
              }
              _2061_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2061_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2075_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2061_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2061_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeVar(_2053_field)), ((_2056_isConstant) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("()")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2075_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2061_s = Dafny.Sequence<Dafny.Rune>.Concat(_2061_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2061_s = Dafny.Sequence<Dafny.Rune>.Concat(_2061_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2077_typeShape;
            _2077_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2078_i;
            _2078_i = BigInteger.Zero;
            while ((_2078_i) < (new BigInteger((_2057_arguments).Count))) {
              if ((_2078_i).Sign == 1) {
                _2077_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2077_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2077_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2077_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2078_i = (_2078_i) + (BigInteger.One);
            }
            _2077_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2077_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2061_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2061_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2077_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2061_s);
            RAST._IExpr _out523;
            DCOMP._IOwnership _out524;
            (this).FromOwned(r, expectedOwnership, out _out523, out _out524);
            r = _out523;
            resultingOwnership = _out524;
            readIdents = _2060_recIdents;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Select) {
          DAST._IExpression _2079_on = _source98.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2080_field = _source98.dtor_field;
          bool _2081_isConstant = _source98.dtor_isConstant;
          bool _2082_isDatatype = _source98.dtor_onDatatype;
          DAST._IType _2083_fieldType = _source98.dtor_fieldType;
          unmatched98 = false;
          {
            if (((_2079_on).is_Companion) || ((_2079_on).is_ExternCompanion)) {
              RAST._IExpr _2084_onExpr;
              DCOMP._IOwnership _2085_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2086_recIdents;
              RAST._IExpr _out525;
              DCOMP._IOwnership _out526;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out527;
              (this).GenExpr(_2079_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out525, out _out526, out _out527);
              _2084_onExpr = _out525;
              _2085_onOwned = _out526;
              _2086_recIdents = _out527;
              r = ((_2084_onExpr).MSel(DCOMP.__default.escapeVar(_2080_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out528;
              DCOMP._IOwnership _out529;
              (this).FromOwned(r, expectedOwnership, out _out528, out _out529);
              r = _out528;
              resultingOwnership = _out529;
              readIdents = _2086_recIdents;
              return ;
            } else if (_2082_isDatatype) {
              RAST._IExpr _2087_onExpr;
              DCOMP._IOwnership _2088_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2089_recIdents;
              RAST._IExpr _out530;
              DCOMP._IOwnership _out531;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out532;
              (this).GenExpr(_2079_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out530, out _out531, out _out532);
              _2087_onExpr = _out530;
              _2088_onOwned = _out531;
              _2089_recIdents = _out532;
              r = ((_2087_onExpr).Sel(DCOMP.__default.escapeVar(_2080_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2090_typ;
              RAST._IType _out533;
              _out533 = (this).GenType(_2083_fieldType, DCOMP.GenTypeContext.@default());
              _2090_typ = _out533;
              RAST._IExpr _out534;
              DCOMP._IOwnership _out535;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out534, out _out535);
              r = _out534;
              resultingOwnership = _out535;
              readIdents = _2089_recIdents;
            } else {
              RAST._IExpr _2091_onExpr;
              DCOMP._IOwnership _2092_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2093_recIdents;
              RAST._IExpr _out536;
              DCOMP._IOwnership _out537;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
              (this).GenExpr(_2079_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out536, out _out537, out _out538);
              _2091_onExpr = _out536;
              _2092_onOwned = _out537;
              _2093_recIdents = _out538;
              r = _2091_onExpr;
              if (!object.Equals(_2091_onExpr, RAST.__default.self)) {
                RAST._IExpr _source100 = _2091_onExpr;
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
              r = (r).Sel(DCOMP.__default.escapeVar(_2080_field));
              if (_2081_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out539;
              DCOMP._IOwnership _out540;
              (this).FromOwned(r, expectedOwnership, out _out539, out _out540);
              r = _out539;
              resultingOwnership = _out540;
              readIdents = _2093_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Index) {
          DAST._IExpression _2094_on = _source98.dtor_expr;
          DAST._ICollKind _2095_collKind = _source98.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2096_indices = _source98.dtor_indices;
          unmatched98 = false;
          {
            RAST._IExpr _2097_onExpr;
            DCOMP._IOwnership _2098_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2099_recIdents;
            RAST._IExpr _out541;
            DCOMP._IOwnership _out542;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out543;
            (this).GenExpr(_2094_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out541, out _out542, out _out543);
            _2097_onExpr = _out541;
            _2098_onOwned = _out542;
            _2099_recIdents = _out543;
            readIdents = _2099_recIdents;
            r = _2097_onExpr;
            bool _2100_hadArray;
            _2100_hadArray = false;
            if (object.Equals(_2095_collKind, DAST.CollKind.create_Array())) {
              r = ((this).read__macro).Apply1(r);
              _2100_hadArray = true;
              if ((new BigInteger((_2096_indices).Count)) > (BigInteger.One)) {
                r = (r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
              }
            }
            BigInteger _hi49 = new BigInteger((_2096_indices).Count);
            for (BigInteger _2101_i = BigInteger.Zero; _2101_i < _hi49; _2101_i++) {
              if (object.Equals(_2095_collKind, DAST.CollKind.create_Array())) {
                RAST._IExpr _2102_idx;
                DCOMP._IOwnership _2103_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2104_recIdentsIdx;
                RAST._IExpr _out544;
                DCOMP._IOwnership _out545;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out546;
                (this).GenExpr((_2096_indices).Select(_2101_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out544, out _out545, out _out546);
                _2102_idx = _out544;
                _2103_idxOwned = _out545;
                _2104_recIdentsIdx = _out546;
                _2102_idx = RAST.__default.IntoUsize(_2102_idx);
                r = RAST.Expr.create_SelectIndex(r, _2102_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2104_recIdentsIdx);
              } else {
                RAST._IExpr _2105_idx;
                DCOMP._IOwnership _2106_idxOwned;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2107_recIdentsIdx;
                RAST._IExpr _out547;
                DCOMP._IOwnership _out548;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
                (this).GenExpr((_2096_indices).Select(_2101_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out547, out _out548, out _out549);
                _2105_idx = _out547;
                _2106_idxOwned = _out548;
                _2107_recIdentsIdx = _out549;
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2105_idx);
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2107_recIdentsIdx);
              }
            }
            if (_2100_hadArray) {
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
          DAST._IExpression _2108_on = _source98.dtor_expr;
          bool _2109_isArray = _source98.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2110_low = _source98.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2111_high = _source98.dtor_high;
          unmatched98 = false;
          {
            RAST._IExpr _2112_onExpr;
            DCOMP._IOwnership _2113_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2114_recIdents;
            RAST._IExpr _out552;
            DCOMP._IOwnership _out553;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out554;
            (this).GenExpr(_2108_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out552, out _out553, out _out554);
            _2112_onExpr = _out552;
            _2113_onOwned = _out553;
            _2114_recIdents = _out554;
            readIdents = _2114_recIdents;
            Dafny.ISequence<Dafny.Rune> _2115_methodName;
            _2115_methodName = (((_2110_low).is_Some) ? ((((_2111_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2111_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2116_arguments;
            _2116_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source101 = _2110_low;
            bool unmatched101 = true;
            if (unmatched101) {
              if (_source101.is_Some) {
                DAST._IExpression _2117_l = _source101.dtor_value;
                unmatched101 = false;
                {
                  RAST._IExpr _2118_lExpr;
                  DCOMP._IOwnership _2119___v199;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2120_recIdentsL;
                  RAST._IExpr _out555;
                  DCOMP._IOwnership _out556;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out557;
                  (this).GenExpr(_2117_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out555, out _out556, out _out557);
                  _2118_lExpr = _out555;
                  _2119___v199 = _out556;
                  _2120_recIdentsL = _out557;
                  _2116_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2116_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2118_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2120_recIdentsL);
                }
              }
            }
            if (unmatched101) {
              unmatched101 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source102 = _2111_high;
            bool unmatched102 = true;
            if (unmatched102) {
              if (_source102.is_Some) {
                DAST._IExpression _2121_h = _source102.dtor_value;
                unmatched102 = false;
                {
                  RAST._IExpr _2122_hExpr;
                  DCOMP._IOwnership _2123___v200;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2124_recIdentsH;
                  RAST._IExpr _out558;
                  DCOMP._IOwnership _out559;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
                  (this).GenExpr(_2121_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out558, out _out559, out _out560);
                  _2122_hExpr = _out558;
                  _2123___v200 = _out559;
                  _2124_recIdentsH = _out560;
                  _2116_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2116_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2122_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2124_recIdentsH);
                }
              }
            }
            if (unmatched102) {
              unmatched102 = false;
            }
            r = _2112_onExpr;
            if (_2109_isArray) {
              if (!(_2115_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2115_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2115_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2115_methodName))).Apply(_2116_arguments);
            } else {
              if (!(_2115_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2115_methodName)).Apply(_2116_arguments);
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
          DAST._IExpression _2125_on = _source98.dtor_expr;
          BigInteger _2126_idx = _source98.dtor_index;
          DAST._IType _2127_fieldType = _source98.dtor_fieldType;
          unmatched98 = false;
          {
            RAST._IExpr _2128_onExpr;
            DCOMP._IOwnership _2129_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2130_recIdents;
            RAST._IExpr _out563;
            DCOMP._IOwnership _out564;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
            (this).GenExpr(_2125_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out563, out _out564, out _out565);
            _2128_onExpr = _out563;
            _2129_onOwnership = _out564;
            _2130_recIdents = _out565;
            Dafny.ISequence<Dafny.Rune> _2131_selName;
            _2131_selName = Std.Strings.__default.OfNat(_2126_idx);
            DAST._IType _source103 = _2127_fieldType;
            bool unmatched103 = true;
            if (unmatched103) {
              if (_source103.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2132_tps = _source103.dtor_Tuple_a0;
                unmatched103 = false;
                if (((_2127_fieldType).is_Tuple) && ((new BigInteger((_2132_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2131_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2131_selName);
                }
              }
            }
            if (unmatched103) {
              unmatched103 = false;
            }
            r = ((_2128_onExpr).Sel(_2131_selName)).Clone();
            RAST._IExpr _out566;
            DCOMP._IOwnership _out567;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out566, out _out567);
            r = _out566;
            resultingOwnership = _out567;
            readIdents = _2130_recIdents;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Call) {
          DAST._IExpression _2133_on = _source98.dtor_on;
          DAST._ICallName _2134_name = _source98.dtor_callName;
          Dafny.ISequence<DAST._IType> _2135_typeArgs = _source98.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2136_args = _source98.dtor_args;
          unmatched98 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2137_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2138_recIdents;
            Dafny.ISequence<RAST._IType> _2139_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2140_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out568;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out569;
            Dafny.ISequence<RAST._IType> _out570;
            Std.Wrappers._IOption<DAST._IResolvedType> _out571;
            (this).GenArgs(selfIdent, _2134_name, _2135_typeArgs, _2136_args, env, out _out568, out _out569, out _out570, out _out571);
            _2137_argExprs = _out568;
            _2138_recIdents = _out569;
            _2139_typeExprs = _out570;
            _2140_fullNameQualifier = _out571;
            readIdents = _2138_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source104 = _2140_fullNameQualifier;
            bool unmatched104 = true;
            if (unmatched104) {
              if (_source104.is_Some) {
                DAST._IResolvedType value11 = _source104.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2141_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2142_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2143_base = value11.dtor_kind;
                unmatched104 = false;
                RAST._IExpr _2144_fullPath;
                RAST._IExpr _out572;
                _out572 = DCOMP.COMP.GenPathExpr(_2141_path, true);
                _2144_fullPath = _out572;
                Dafny.ISequence<RAST._IType> _2145_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out573;
                _out573 = (this).GenTypeArgs(_2142_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2145_onTypeExprs = _out573;
                RAST._IExpr _2146_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2147_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2148_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2143_base).is_Trait) || ((_2143_base).is_Class)) {
                  RAST._IExpr _out574;
                  DCOMP._IOwnership _out575;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out576;
                  (this).GenExpr(_2133_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out574, out _out575, out _out576);
                  _2146_onExpr = _out574;
                  _2147_recOwnership = _out575;
                  _2148_recIdents = _out576;
                  _2146_onExpr = ((this).read__macro).Apply1(_2146_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2148_recIdents);
                } else {
                  RAST._IExpr _out577;
                  DCOMP._IOwnership _out578;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out579;
                  (this).GenExpr(_2133_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out577, out _out578, out _out579);
                  _2146_onExpr = _out577;
                  _2147_recOwnership = _out578;
                  _2148_recIdents = _out579;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2148_recIdents);
                }
                r = ((((_2144_fullPath).ApplyType(_2145_onTypeExprs)).MSel(DCOMP.__default.escapeName((_2134_name).dtor_name))).ApplyType(_2139_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2146_onExpr), _2137_argExprs));
                RAST._IExpr _out580;
                DCOMP._IOwnership _out581;
                (this).FromOwned(r, expectedOwnership, out _out580, out _out581);
                r = _out580;
                resultingOwnership = _out581;
              }
            }
            if (unmatched104) {
              unmatched104 = false;
              RAST._IExpr _2149_onExpr;
              DCOMP._IOwnership _2150___v206;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2151_recIdents;
              RAST._IExpr _out582;
              DCOMP._IOwnership _out583;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out584;
              (this).GenExpr(_2133_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out582, out _out583, out _out584);
              _2149_onExpr = _out582;
              _2150___v206 = _out583;
              _2151_recIdents = _out584;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2151_recIdents);
              Dafny.ISequence<Dafny.Rune> _2152_renderedName;
              _2152_renderedName = (this).GetMethodName(_2133_on, _2134_name);
              DAST._IExpression _source105 = _2133_on;
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
                    _2149_onExpr = (_2149_onExpr).MSel(_2152_renderedName);
                  }
                }
              }
              if (unmatched105) {
                unmatched105 = false;
                {
                  if (!object.Equals(_2149_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source106 = _2134_name;
                    bool unmatched106 = true;
                    if (unmatched106) {
                      if (_source106.is_CallName) {
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source106.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2153_tpe = onType2.dtor_value;
                          unmatched106 = false;
                          RAST._IType _2154_typ;
                          RAST._IType _out585;
                          _out585 = (this).GenType(_2153_tpe, DCOMP.GenTypeContext.@default());
                          _2154_typ = _out585;
                          if ((_2154_typ).IsObjectOrPointer()) {
                            _2149_onExpr = ((this).read__macro).Apply1(_2149_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched106) {
                      unmatched106 = false;
                    }
                  }
                  _2149_onExpr = (_2149_onExpr).Sel(_2152_renderedName);
                }
              }
              r = ((_2149_onExpr).ApplyType(_2139_typeExprs)).Apply(_2137_argExprs);
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
          Dafny.ISequence<DAST._IFormal> _2155_paramsDafny = _source98.dtor_params;
          DAST._IType _2156_retType = _source98.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2157_body = _source98.dtor_body;
          unmatched98 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2158_params;
            Dafny.ISequence<RAST._IFormal> _out588;
            _out588 = (this).GenParams(_2155_paramsDafny, true);
            _2158_params = _out588;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2159_paramNames;
            _2159_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2160_paramTypesMap;
            _2160_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi50 = new BigInteger((_2158_params).Count);
            for (BigInteger _2161_i = BigInteger.Zero; _2161_i < _hi50; _2161_i++) {
              Dafny.ISequence<Dafny.Rune> _2162_name;
              _2162_name = ((_2158_params).Select(_2161_i)).dtor_name;
              _2159_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2159_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2162_name));
              _2160_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2160_paramTypesMap, _2162_name, ((_2158_params).Select(_2161_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2163_subEnv;
            _2163_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2159_paramNames, _2160_paramTypesMap));
            RAST._IExpr _2164_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2165_recIdents;
            DCOMP._IEnvironment _2166___v216;
            RAST._IExpr _out589;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out590;
            DCOMP._IEnvironment _out591;
            (this).GenStmts(_2157_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2163_subEnv, true, Std.Wrappers.Option<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>.create_None(), out _out589, out _out590, out _out591);
            _2164_recursiveGen = _out589;
            _2165_recIdents = _out590;
            _2166___v216 = _out591;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2165_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2165_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2167_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll7 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_7 in (_2167_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2168_name = (Dafny.ISequence<Dafny.Rune>)_compr_7;
                if ((_2167_paramNames).Contains(_2168_name)) {
                  _coll7.Add(_2168_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll7);
            }))())(_2159_paramNames));
            RAST._IExpr _2169_allReadCloned;
            _2169_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2165_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2170_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2165_recIdents).Elements) {
                _2170_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_2165_recIdents).Contains(_2170_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 5099)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2170_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2171_selfCloned;
                DCOMP._IOwnership _2172___v217;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2173___v218;
                RAST._IExpr _out592;
                DCOMP._IOwnership _out593;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out592, out _out593, out _out594);
                _2171_selfCloned = _out592;
                _2172___v217 = _out593;
                _2173___v218 = _out594;
                _2169_allReadCloned = (_2169_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2171_selfCloned)));
              } else if (!((_2159_paramNames).Contains(_2170_next))) {
                RAST._IExpr _2174_copy;
                _2174_copy = (RAST.Expr.create_Identifier(_2170_next)).Clone();
                _2169_allReadCloned = (_2169_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2170_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2174_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2170_next));
              }
              _2165_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2165_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2170_next));
            }
            RAST._IType _2175_retTypeGen;
            RAST._IType _out595;
            _out595 = (this).GenType(_2156_retType, DCOMP.GenTypeContext.InFn());
            _2175_retTypeGen = _out595;
            r = RAST.Expr.create_Block((_2169_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2158_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2175_retTypeGen), RAST.Expr.create_Block(_2164_recursiveGen)))));
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
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2176_values = _source98.dtor_values;
          DAST._IType _2177_retType = _source98.dtor_retType;
          DAST._IExpression _2178_expr = _source98.dtor_expr;
          unmatched98 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2179_paramNames;
            _2179_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2180_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out598;
            _out598 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2181_value) => {
              return (_2181_value).dtor__0;
            })), _2176_values), false);
            _2180_paramFormals = _out598;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2182_paramTypes;
            _2182_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2183_paramNamesSet;
            _2183_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi51 = new BigInteger((_2176_values).Count);
            for (BigInteger _2184_i = BigInteger.Zero; _2184_i < _hi51; _2184_i++) {
              Dafny.ISequence<Dafny.Rune> _2185_name;
              _2185_name = (((_2176_values).Select(_2184_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2186_rName;
              _2186_rName = DCOMP.__default.escapeVar(_2185_name);
              _2179_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2179_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2186_rName));
              _2182_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2182_paramTypes, _2186_rName, ((_2180_paramFormals).Select(_2184_i)).dtor_tpe);
              _2183_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2183_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2186_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi52 = new BigInteger((_2176_values).Count);
            for (BigInteger _2187_i = BigInteger.Zero; _2187_i < _hi52; _2187_i++) {
              RAST._IType _2188_typeGen;
              RAST._IType _out599;
              _out599 = (this).GenType((((_2176_values).Select(_2187_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2188_typeGen = _out599;
              RAST._IExpr _2189_valueGen;
              DCOMP._IOwnership _2190___v219;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2191_recIdents;
              RAST._IExpr _out600;
              DCOMP._IOwnership _out601;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out602;
              (this).GenExpr(((_2176_values).Select(_2187_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out600, out _out601, out _out602);
              _2189_valueGen = _out600;
              _2190___v219 = _out601;
              _2191_recIdents = _out602;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar((((_2176_values).Select(_2187_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2188_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2189_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2191_recIdents);
            }
            DCOMP._IEnvironment _2192_newEnv;
            _2192_newEnv = DCOMP.Environment.create(_2179_paramNames, _2182_paramTypes);
            RAST._IExpr _2193_recGen;
            DCOMP._IOwnership _2194_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2195_recIdents;
            RAST._IExpr _out603;
            DCOMP._IOwnership _out604;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out605;
            (this).GenExpr(_2178_expr, selfIdent, _2192_newEnv, expectedOwnership, out _out603, out _out604, out _out605);
            _2193_recGen = _out603;
            _2194_recOwned = _out604;
            _2195_recIdents = _out605;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2195_recIdents, _2183_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2193_recGen));
            RAST._IExpr _out606;
            DCOMP._IOwnership _out607;
            (this).FromOwnership(r, _2194_recOwned, expectedOwnership, out _out606, out _out607);
            r = _out606;
            resultingOwnership = _out607;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2196_name = _source98.dtor_ident;
          DAST._IType _2197_tpe = _source98.dtor_typ;
          DAST._IExpression _2198_value = _source98.dtor_value;
          DAST._IExpression _2199_iifeBody = _source98.dtor_iifeBody;
          unmatched98 = false;
          {
            RAST._IExpr _2200_valueGen;
            DCOMP._IOwnership _2201___v220;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2202_recIdents;
            RAST._IExpr _out608;
            DCOMP._IOwnership _out609;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
            (this).GenExpr(_2198_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out608, out _out609, out _out610);
            _2200_valueGen = _out608;
            _2201___v220 = _out609;
            _2202_recIdents = _out610;
            readIdents = _2202_recIdents;
            RAST._IType _2203_valueTypeGen;
            RAST._IType _out611;
            _out611 = (this).GenType(_2197_tpe, DCOMP.GenTypeContext.InFn());
            _2203_valueTypeGen = _out611;
            RAST._IExpr _2204_bodyGen;
            DCOMP._IOwnership _2205___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2206_bodyIdents;
            RAST._IExpr _out612;
            DCOMP._IOwnership _out613;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out614;
            (this).GenExpr(_2199_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out612, out _out613, out _out614);
            _2204_bodyGen = _out612;
            _2205___v221 = _out613;
            _2206_bodyIdents = _out614;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2206_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeVar(_2196_name))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeVar(_2196_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2203_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2200_valueGen))).Then(_2204_bodyGen));
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
          DAST._IExpression _2207_func = _source98.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2208_args = _source98.dtor_args;
          unmatched98 = false;
          {
            RAST._IExpr _2209_funcExpr;
            DCOMP._IOwnership _2210___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2211_recIdents;
            RAST._IExpr _out617;
            DCOMP._IOwnership _out618;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out619;
            (this).GenExpr(_2207_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out617, out _out618, out _out619);
            _2209_funcExpr = _out617;
            _2210___v222 = _out618;
            _2211_recIdents = _out619;
            readIdents = _2211_recIdents;
            Dafny.ISequence<RAST._IExpr> _2212_rArgs;
            _2212_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi53 = new BigInteger((_2208_args).Count);
            for (BigInteger _2213_i = BigInteger.Zero; _2213_i < _hi53; _2213_i++) {
              RAST._IExpr _2214_argExpr;
              DCOMP._IOwnership _2215_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2216_argIdents;
              RAST._IExpr _out620;
              DCOMP._IOwnership _out621;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out622;
              (this).GenExpr((_2208_args).Select(_2213_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out620, out _out621, out _out622);
              _2214_argExpr = _out620;
              _2215_argOwned = _out621;
              _2216_argIdents = _out622;
              _2212_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2212_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2214_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2216_argIdents);
            }
            r = (_2209_funcExpr).Apply(_2212_rArgs);
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
          DAST._IExpression _2217_on = _source98.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2218_dType = _source98.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2219_variant = _source98.dtor_variant;
          unmatched98 = false;
          {
            RAST._IExpr _2220_exprGen;
            DCOMP._IOwnership _2221___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2222_recIdents;
            RAST._IExpr _out625;
            DCOMP._IOwnership _out626;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out627;
            (this).GenExpr(_2217_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out625, out _out626, out _out627);
            _2220_exprGen = _out625;
            _2221___v223 = _out626;
            _2222_recIdents = _out627;
            RAST._IType _2223_dTypePath;
            RAST._IType _out628;
            _out628 = DCOMP.COMP.GenPath(_2218_dType);
            _2223_dTypePath = _out628;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2220_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2223_dTypePath).MSel(DCOMP.__default.escapeName(_2219_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out629;
            DCOMP._IOwnership _out630;
            (this).FromOwned(r, expectedOwnership, out _out629, out _out630);
            r = _out629;
            resultingOwnership = _out630;
            readIdents = _2222_recIdents;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_Is) {
          DAST._IExpression _2224_expr = _source98.dtor_expr;
          DAST._IType _2225_fromType = _source98.dtor_fromType;
          DAST._IType _2226_toType = _source98.dtor_toType;
          unmatched98 = false;
          {
            RAST._IExpr _2227_expr;
            DCOMP._IOwnership _2228_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2229_recIdents;
            RAST._IExpr _out631;
            DCOMP._IOwnership _out632;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out633;
            (this).GenExpr(_2224_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out631, out _out632, out _out633);
            _2227_expr = _out631;
            _2228_recOwned = _out632;
            _2229_recIdents = _out633;
            RAST._IType _2230_fromType;
            RAST._IType _out634;
            _out634 = (this).GenType(_2225_fromType, DCOMP.GenTypeContext.@default());
            _2230_fromType = _out634;
            RAST._IType _2231_toType;
            RAST._IType _out635;
            _out635 = (this).GenType(_2226_toType, DCOMP.GenTypeContext.@default());
            _2231_toType = _out635;
            if (((_2230_fromType).IsObject()) && ((_2231_toType).IsObject())) {
              r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is_instance_of_object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements((_2230_fromType).ObjectOrPointerUnderlying(), (_2231_toType).ObjectOrPointerUnderlying()))).Apply1(_2227_expr);
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Source and/or target types of type test is/are not Object"));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            }
            RAST._IExpr _out636;
            DCOMP._IOwnership _out637;
            (this).FromOwnership(r, _2228_recOwned, expectedOwnership, out _out636, out _out637);
            r = _out636;
            resultingOwnership = _out637;
            readIdents = _2229_recIdents;
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
          DAST._IExpression _2232_of = _source98.dtor_of;
          unmatched98 = false;
          {
            RAST._IExpr _2233_exprGen;
            DCOMP._IOwnership _2234___v224;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2235_recIdents;
            RAST._IExpr _out640;
            DCOMP._IOwnership _out641;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out642;
            (this).GenExpr(_2232_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out640, out _out641, out _out642);
            _2233_exprGen = _out640;
            _2234___v224 = _out641;
            _2235_recIdents = _out642;
            r = ((_2233_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            (this).FromOwned(r, expectedOwnership, out _out643, out _out644);
            r = _out643;
            resultingOwnership = _out644;
            readIdents = _2235_recIdents;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_SeqBoundedPool) {
          DAST._IExpression _2236_of = _source98.dtor_of;
          bool _2237_includeDuplicates = _source98.dtor_includeDuplicates;
          unmatched98 = false;
          {
            RAST._IExpr _2238_exprGen;
            DCOMP._IOwnership _2239___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2240_recIdents;
            RAST._IExpr _out645;
            DCOMP._IOwnership _out646;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out647;
            (this).GenExpr(_2236_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out645, out _out646, out _out647);
            _2238_exprGen = _out645;
            _2239___v225 = _out646;
            _2240_recIdents = _out647;
            r = ((_2238_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2237_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out648;
            DCOMP._IOwnership _out649;
            (this).FromOwned(r, expectedOwnership, out _out648, out _out649);
            r = _out648;
            resultingOwnership = _out649;
            readIdents = _2240_recIdents;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_MapBoundedPool) {
          DAST._IExpression _2241_of = _source98.dtor_of;
          unmatched98 = false;
          {
            RAST._IExpr _2242_exprGen;
            DCOMP._IOwnership _2243___v226;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2244_recIdents;
            RAST._IExpr _out650;
            DCOMP._IOwnership _out651;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out652;
            (this).GenExpr(_2241_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out650, out _out651, out _out652);
            _2242_exprGen = _out650;
            _2243___v226 = _out651;
            _2244_recIdents = _out652;
            r = ((((_2242_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2244_recIdents;
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
          DAST._IExpression _2245_lo = _source98.dtor_lo;
          DAST._IExpression _2246_hi = _source98.dtor_hi;
          bool _2247_up = _source98.dtor_up;
          unmatched98 = false;
          {
            RAST._IExpr _2248_lo;
            DCOMP._IOwnership _2249___v227;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2250_recIdentsLo;
            RAST._IExpr _out655;
            DCOMP._IOwnership _out656;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out657;
            (this).GenExpr(_2245_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out655, out _out656, out _out657);
            _2248_lo = _out655;
            _2249___v227 = _out656;
            _2250_recIdentsLo = _out657;
            RAST._IExpr _2251_hi;
            DCOMP._IOwnership _2252___v228;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2253_recIdentsHi;
            RAST._IExpr _out658;
            DCOMP._IOwnership _out659;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out660;
            (this).GenExpr(_2246_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out658, out _out659, out _out660);
            _2251_hi = _out658;
            _2252___v228 = _out659;
            _2253_recIdentsHi = _out660;
            if (_2247_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2248_lo, _2251_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2251_hi, _2248_lo));
            }
            RAST._IExpr _out661;
            DCOMP._IOwnership _out662;
            (this).FromOwned(r, expectedOwnership, out _out661, out _out662);
            r = _out661;
            resultingOwnership = _out662;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2250_recIdentsLo, _2253_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_UnboundedIntRange) {
          DAST._IExpression _2254_start = _source98.dtor_start;
          bool _2255_up = _source98.dtor_up;
          unmatched98 = false;
          {
            RAST._IExpr _2256_start;
            DCOMP._IOwnership _2257___v229;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2258_recIdentStart;
            RAST._IExpr _out663;
            DCOMP._IOwnership _out664;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out665;
            (this).GenExpr(_2254_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out663, out _out664, out _out665);
            _2256_start = _out663;
            _2257___v229 = _out664;
            _2258_recIdentStart = _out665;
            if (_2255_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2256_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2256_start);
            }
            RAST._IExpr _out666;
            DCOMP._IOwnership _out667;
            (this).FromOwned(r, expectedOwnership, out _out666, out _out667);
            r = _out666;
            resultingOwnership = _out667;
            readIdents = _2258_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched98) {
        if (_source98.is_MapBuilder) {
          DAST._IType _2259_keyType = _source98.dtor_keyType;
          DAST._IType _2260_valueType = _source98.dtor_valueType;
          unmatched98 = false;
          {
            RAST._IType _2261_kType;
            RAST._IType _out668;
            _out668 = (this).GenType(_2259_keyType, DCOMP.GenTypeContext.@default());
            _2261_kType = _out668;
            RAST._IType _2262_vType;
            RAST._IType _out669;
            _out669 = (this).GenType(_2260_valueType, DCOMP.GenTypeContext.@default());
            _2262_vType = _out669;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2261_kType, _2262_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IType _2263_elemType = _source98.dtor_elemType;
          unmatched98 = false;
          {
            RAST._IType _2264_eType;
            RAST._IType _out672;
            _out672 = (this).GenType(_2263_elemType, DCOMP.GenTypeContext.@default());
            _2264_eType = _out672;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2264_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
        DAST._IType _2265_elemType = _source98.dtor_elemType;
        DAST._IExpression _2266_collection = _source98.dtor_collection;
        bool _2267_is__forall = _source98.dtor_is__forall;
        DAST._IExpression _2268_lambda = _source98.dtor_lambda;
        unmatched98 = false;
        {
          RAST._IType _2269_tpe;
          RAST._IType _out675;
          _out675 = (this).GenType(_2265_elemType, DCOMP.GenTypeContext.@default());
          _2269_tpe = _out675;
          RAST._IExpr _2270_collectionGen;
          DCOMP._IOwnership _2271___v230;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2272_recIdents;
          RAST._IExpr _out676;
          DCOMP._IOwnership _out677;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out678;
          (this).GenExpr(_2266_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out676, out _out677, out _out678);
          _2270_collectionGen = _out676;
          _2271___v230 = _out677;
          _2272_recIdents = _out678;
          Dafny.ISequence<DAST._IAttribute> _2273_extraAttributes;
          _2273_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2266_collection).is_IntRange) || ((_2266_collection).is_UnboundedIntRange)) || ((_2266_collection).is_SeqBoundedPool)) {
            _2273_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2268_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2274_formals;
            _2274_formals = (_2268_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2275_newFormals;
            _2275_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi54 = new BigInteger((_2274_formals).Count);
            for (BigInteger _2276_i = BigInteger.Zero; _2276_i < _hi54; _2276_i++) {
              var _pat_let_tv147 = _2273_extraAttributes;
              var _pat_let_tv148 = _2274_formals;
              _2275_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2275_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2274_formals).Select(_2276_i), _pat_let38_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let38_0, _2277_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv147, ((_pat_let_tv148).Select(_2276_i)).dtor_attributes), _pat_let39_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let39_0, _2278_dt__update_hattributes_h0 => DAST.Formal.create((_2277_dt__update__tmp_h0).dtor_name, (_2277_dt__update__tmp_h0).dtor_typ, _2278_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv149 = _2275_newFormals;
            DAST._IExpression _2279_newLambda;
            _2279_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2268_lambda, _pat_let40_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let40_0, _2280_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv149, _pat_let41_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let41_0, _2281_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2281_dt__update_hparams_h0, (_2280_dt__update__tmp_h1).dtor_retType, (_2280_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2282_lambdaGen;
            DCOMP._IOwnership _2283___v231;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2284_recLambdaIdents;
            RAST._IExpr _out679;
            DCOMP._IOwnership _out680;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out681;
            (this).GenExpr(_2279_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out679, out _out680, out _out681);
            _2282_lambdaGen = _out679;
            _2283___v231 = _out680;
            _2284_recLambdaIdents = _out681;
            Dafny.ISequence<Dafny.Rune> _2285_fn;
            _2285_fn = ((_2267_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2270_collectionGen).Sel(_2285_fn)).Apply1(((_2282_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2272_recIdents, _2284_recLambdaIdents);
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
      Dafny.ISequence<RAST._IModDecl> _2286_externUseDecls;
      _2286_externUseDecls = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi55 = new BigInteger((externalFiles).Count);
      for (BigInteger _2287_i = BigInteger.Zero; _2287_i < _hi55; _2287_i++) {
        Dafny.ISequence<Dafny.Rune> _2288_externalFile;
        _2288_externalFile = (externalFiles).Select(_2287_i);
        Dafny.ISequence<Dafny.Rune> _2289_externalMod;
        _2289_externalMod = _2288_externalFile;
        if (((new BigInteger((_2288_externalFile).Count)) > (new BigInteger(3))) && (((_2288_externalFile).Drop((new BigInteger((_2288_externalFile).Count)) - (new BigInteger(3)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".rs")))) {
          _2289_externalMod = (_2288_externalFile).Subsequence(BigInteger.Zero, (new BigInteger((_2288_externalFile).Count)) - (new BigInteger(3)));
        } else {
          (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unrecognized external file "), _2288_externalFile), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(". External file must be *.rs files")));
        }
        RAST._IMod _2290_externMod;
        _2290_externMod = RAST.Mod.create_ExternMod(_2289_externalMod);
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (_2290_externMod)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        _2286_externUseDecls = Dafny.Sequence<RAST._IModDecl>.Concat(_2286_externUseDecls, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_UseDecl(RAST.Use.create(RAST.Visibility.create_PUB(), ((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"))).MSel(_2289_externalMod)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"))))));
      }
      if (!(_2286_externUseDecls).Equals(Dafny.Sequence<RAST._IModDecl>.FromElements())) {
        s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(s, (RAST.Mod.create_Mod(DCOMP.COMP.DAFNY__EXTERN__MODULE, _2286_externUseDecls))._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
      }
      BigInteger _hi56 = new BigInteger((p).Count);
      for (BigInteger _2291_i = BigInteger.Zero; _2291_i < _hi56; _2291_i++) {
        RAST._IMod _2292_m;
        RAST._IMod _out684;
        _out684 = (this).GenModule((p).Select(_2291_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2292_m = _out684;
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, (_2292_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")));
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2293_i;
      _2293_i = BigInteger.Zero;
      while ((_2293_i) < (new BigInteger((fullName).Count))) {
        if ((_2293_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2293_i)));
        _2293_i = (_2293_i) + (BigInteger.One);
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