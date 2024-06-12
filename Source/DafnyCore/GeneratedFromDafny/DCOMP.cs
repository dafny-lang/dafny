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
      Dafny.ISequence<Dafny.Rune> _1065___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1065___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1065___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1065___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in123 = (i).Drop(new BigInteger(2));
        i = _in123;
        goto TAIL_CALL_START;
      } else {
        _1065___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1065___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(BigInteger.One);
        i = _in124;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1066___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1066___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1066___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1066___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      } else {
        _1066___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1066___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1067_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1067_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeField(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1068_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1068_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1068_r);
      } else {
        return DCOMP.__default.escapeName(f);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeDtor(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1069_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1069_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1069_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": r#_")), _1069_r);
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
      var _pat_let_tv104 = dafnyName;
      var _pat_let_tv105 = rs;
      var _pat_let_tv106 = dafnyName;
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _1070_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source47 = (rs).Select(BigInteger.Zero);
          bool unmatched47 = true;
          if (unmatched47) {
            if (_source47.is_UserDefined) {
              DAST._IResolvedType _1071_resolvedType = _source47.dtor_resolved;
              unmatched47 = false;
              return DCOMP.__default.TraitTypeContainingMethod(_1071_resolvedType, _pat_let_tv104);
            }
          }
          if (unmatched47) {
            DAST._IType _1072___v44 = _source47;
            unmatched47 = false;
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
          throw new System.Exception("unexpected control point");
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source48 = _1070_res;
        bool unmatched48 = true;
        if (unmatched48) {
          if (_source48.is_Some) {
            DAST._IResolvedType _1073___v45 = _source48.dtor_value;
            unmatched48 = false;
            return _1070_res;
          }
        }
        if (unmatched48) {
          unmatched48 = false;
          return DCOMP.__default.TraitTypeContainingMethodAux((_pat_let_tv105).Drop(BigInteger.One), _pat_let_tv106);
        }
        throw new System.Exception("unexpected control point");
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethod(DAST._IResolvedType r, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DAST._IResolvedType _let_tmp_rhs52 = r;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1074_path = _let_tmp_rhs52.dtor_path;
      Dafny.ISequence<DAST._IType> _1075_typeArgs = _let_tmp_rhs52.dtor_typeArgs;
      DAST._IResolvedTypeBase _1076_kind = _let_tmp_rhs52.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1077_attributes = _let_tmp_rhs52.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1078_properMethods = _let_tmp_rhs52.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1079_extendedTypes = _let_tmp_rhs52.dtor_extendedTypes;
      if ((_1078_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1079_extendedTypes, dafnyName);
      }
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
      BigInteger _1080_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1080_indexInEnv), ((this).dtor_names).Drop((_1080_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
    public Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> error {get; set;}
    public void __ctor(bool unicodeChars, DCOMP._IObjectType objectType)
    {
      (this)._UnicodeChars = unicodeChars;
      (this)._ObjectType = objectType;
      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
    }
    public RAST._IMod GenModule(DAST._IModule mod, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      RAST._IMod s = RAST.Mod.Default();
      Dafny.ISequence<Dafny.Rune> _1081_modName;
      _1081_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1081_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1082_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1082_body = _out15;
        s = RAST.Mod.create_Mod(_1081_modName, _1082_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _1083_i = BigInteger.Zero; _1083_i < _hi5; _1083_i++) {
        Dafny.ISequence<RAST._IModDecl> _1084_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source49 = (body).Select(_1083_i);
        bool unmatched49 = true;
        if (unmatched49) {
          if (_source49.is_Module) {
            DAST._IModule _1085_m = _source49.dtor_Module_a0;
            unmatched49 = false;
            RAST._IMod _1086_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1085_m, containingPath);
            _1086_mm = _out16;
            _1084_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1086_mm));
          }
        }
        if (unmatched49) {
          if (_source49.is_Class) {
            DAST._IClass _1087_c = _source49.dtor_Class_a0;
            unmatched49 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1087_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1087_c).dtor_name)));
            _1084_generated = _out17;
          }
        }
        if (unmatched49) {
          if (_source49.is_Trait) {
            DAST._ITrait _1088_t = _source49.dtor_Trait_a0;
            unmatched49 = false;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenTrait(_1088_t, containingPath);
            _1084_generated = _out18;
          }
        }
        if (unmatched49) {
          if (_source49.is_Newtype) {
            DAST._INewtype _1089_n = _source49.dtor_Newtype_a0;
            unmatched49 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1089_n);
            _1084_generated = _out19;
          }
        }
        if (unmatched49) {
          if (_source49.is_SynonymType) {
            DAST._ISynonymType _1090_s = _source49.dtor_SynonymType_a0;
            unmatched49 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1090_s);
            _1084_generated = _out20;
          }
        }
        if (unmatched49) {
          DAST._IDatatype _1091_d = _source49.dtor_Datatype_a0;
          unmatched49 = false;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1091_d);
          _1084_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1084_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1092_genTpConstraint;
      _1092_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1092_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1092_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1092_genTpConstraint);
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
        BigInteger _hi6 = new BigInteger((@params).Count);
        for (BigInteger _1093_tpI = BigInteger.Zero; _1093_tpI < _hi6; _1093_tpI++) {
          DAST._ITypeArgDecl _1094_tp;
          _1094_tp = (@params).Select(_1093_tpI);
          DAST._IType _1095_typeArg;
          RAST._ITypeParamDecl _1096_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1094_tp, out _out22, out _out23);
          _1095_typeArg = _out22;
          _1096_typeParam = _out23;
          RAST._IType _1097_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1095_typeArg, DCOMP.GenTypeContext.@default());
          _1097_rType = _out24;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1095_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1097_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1096_typeParam));
        }
      }
    }
    public bool IsSameResolvedType(DAST._IResolvedType r1, DAST._IResolvedType r2)
    {
      return ((((r1).dtor_path).Equals((r2).dtor_path)) && (((r1).dtor_typeArgs).Equals((r2).dtor_typeArgs))) && (object.Equals((r1).dtor_kind, (r2).dtor_kind));
    }
    public Dafny.ISequence<RAST._IModDecl> GenClass(DAST._IClass c, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> path)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1098_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1099_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1100_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1101_whereConstraints;
      Dafny.ISequence<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1098_typeParamsSeq = _out25;
      _1099_rTypeParams = _out26;
      _1100_rTypeParamsDecls = _out27;
      _1101_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1102_constrainedTypeParams;
      _1102_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1100_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1103_fields;
      _1103_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1104_fieldInits;
      _1104_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1105_fieldI = BigInteger.Zero; _1105_fieldI < _hi7; _1105_fieldI++) {
        DAST._IField _1106_field;
        _1106_field = ((c).dtor_fields).Select(_1105_fieldI);
        RAST._IType _1107_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1106_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1107_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1108_fieldRustName;
        _1108_fieldRustName = DCOMP.__default.escapeName(((_1106_field).dtor_formal).dtor_name);
        _1103_fields = Dafny.Sequence<RAST._IField>.Concat(_1103_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1108_fieldRustName, _1107_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source50 = (_1106_field).dtor_defaultValue;
        bool unmatched50 = true;
        if (unmatched50) {
          if (_source50.is_Some) {
            DAST._IExpression _1109_e = _source50.dtor_value;
            unmatched50 = false;
            {
              RAST._IExpr _1110_expr;
              DCOMP._IOwnership _1111___v46;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1112___v47;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1109_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1110_expr = _out30;
              _1111___v46 = _out31;
              _1112___v47 = _out32;
              _1104_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1104_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1108_fieldRustName, _1110_expr)));
            }
          }
        }
        if (unmatched50) {
          unmatched50 = false;
          {
            RAST._IExpr _1113_default;
            _1113_default = RAST.__default.std__Default__default;
            if ((_1107_fieldType).IsObjectOrPointer()) {
              _1113_default = (_1107_fieldType).ToNullExpr();
            }
            _1104_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1104_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1108_fieldRustName, _1113_default)));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1114_typeParamI = BigInteger.Zero; _1114_typeParamI < _hi8; _1114_typeParamI++) {
        DAST._IType _1115_typeArg;
        RAST._ITypeParamDecl _1116_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1114_typeParamI), out _out33, out _out34);
        _1115_typeArg = _out33;
        _1116_typeParam = _out34;
        RAST._IType _1117_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1115_typeArg, DCOMP.GenTypeContext.@default());
        _1117_rTypeArg = _out35;
        _1103_fields = Dafny.Sequence<RAST._IField>.Concat(_1103_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1114_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1117_rTypeArg))))));
        _1104_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1104_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1114_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1118_datatypeName;
      _1118_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1119_struct;
      _1119_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1118_datatypeName, _1100_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1103_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1119_struct));
      Dafny.ISequence<RAST._IImplMember> _1120_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1121_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1098_typeParamsSeq, out _out36, out _out37);
      _1120_implBodyRaw = _out36;
      _1121_traitBodies = _out37;
      Dafny.ISequence<RAST._IImplMember> _1122_implBody;
      _1122_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.Type.create_SelfOwned())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel((this).allocate)).ApplyType1(RAST.Type.create_SelfOwned())).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1120_implBodyRaw);
      RAST._IImpl _1123_i;
      _1123_i = RAST.Impl.create_Impl(_1100_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1118_datatypeName), _1099_rTypeParams), _1101_whereConstraints, _1122_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1123_i)));
      RAST._IType _1124_genSelfPath;
      RAST._IType _out38;
      _out38 = DCOMP.COMP.GenPath(path);
      _1124_genSelfPath = _out38;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1100_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"))))), RAST.Type.create_TypeApp(_1124_genSelfPath, _1099_rTypeParams), _1101_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any")))))))))));
      BigInteger _hi9 = new BigInteger(((c).dtor_superClasses).Count);
      for (BigInteger _1125_i = BigInteger.Zero; _1125_i < _hi9; _1125_i++) {
        DAST._IType _1126_superClass;
        _1126_superClass = ((c).dtor_superClasses).Select(_1125_i);
        DAST._IType _source51 = _1126_superClass;
        bool unmatched51 = true;
        if (unmatched51) {
          if (_source51.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source51.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1127_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1128_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<DAST._IAttribute> _1129___v48 = resolved0.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1130___v49 = resolved0.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1131___v50 = resolved0.dtor_extendedTypes;
              unmatched51 = false;
              {
                RAST._IType _1132_pathStr;
                RAST._IType _out39;
                _out39 = DCOMP.COMP.GenPath(_1127_traitPath);
                _1132_pathStr = _out39;
                Dafny.ISequence<RAST._IType> _1133_typeArgs;
                Dafny.ISequence<RAST._IType> _out40;
                _out40 = (this).GenTypeArgs(_1128_typeArgs, DCOMP.GenTypeContext.@default());
                _1133_typeArgs = _out40;
                Dafny.ISequence<RAST._IImplMember> _1134_body;
                _1134_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1121_traitBodies).Contains(_1127_traitPath)) {
                  _1134_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1121_traitBodies,_1127_traitPath);
                }
                RAST._IType _1135_traitType;
                _1135_traitType = RAST.Type.create_TypeApp(_1132_pathStr, _1133_typeArgs);
                RAST._IModDecl _1136_x;
                _1136_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1100_rTypeParamsDecls, _1135_traitType, RAST.Type.create_TypeApp(_1124_genSelfPath, _1099_rTypeParams), _1101_whereConstraints, _1134_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1136_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1100_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1135_traitType))), RAST.Type.create_TypeApp(_1124_genSelfPath, _1099_rTypeParams), _1101_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1135_traitType)))))))));
              }
            }
          }
        }
        if (unmatched51) {
          DAST._IType _1137___v51 = _source51;
          unmatched51 = false;
        }
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1138_typeParamsSeq;
      _1138_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1139_typeParamDecls;
      _1139_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1140_typeParams;
      _1140_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi10 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1141_tpI = BigInteger.Zero; _1141_tpI < _hi10; _1141_tpI++) {
          DAST._ITypeArgDecl _1142_tp;
          _1142_tp = ((t).dtor_typeParams).Select(_1141_tpI);
          DAST._IType _1143_typeArg;
          RAST._ITypeParamDecl _1144_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1142_tp, out _out41, out _out42);
          _1143_typeArg = _out41;
          _1144_typeParamDecl = _out42;
          _1138_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1138_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1143_typeArg));
          _1139_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1139_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1144_typeParamDecl));
          RAST._IType _1145_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1143_typeArg, DCOMP.GenTypeContext.@default());
          _1145_typeParam = _out43;
          _1140_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1140_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1145_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1146_fullPath;
      _1146_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1147_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1148___v52;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1146_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1138_typeParamsSeq, out _out44, out _out45);
      _1147_implBody = _out44;
      _1148___v52 = _out45;
      Dafny.ISequence<RAST._IType> _1149_parents;
      _1149_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi11 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1150_i = BigInteger.Zero; _1150_i < _hi11; _1150_i++) {
        RAST._IType _1151_tpe;
        RAST._IType _out46;
        _out46 = (this).GenType(((t).dtor_parents).Select(_1150_i), DCOMP.GenTypeContext.ForTraitParents());
        _1151_tpe = _out46;
        _1149_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1149_parents, Dafny.Sequence<RAST._IType>.FromElements(_1151_tpe)), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply1(RAST.Type.create_DynType(_1151_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1139_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1140_typeParams), _1149_parents, _1147_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1152_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1153_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1154_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1155_whereConstraints;
      Dafny.ISequence<DAST._IType> _out47;
      Dafny.ISequence<RAST._IType> _out48;
      Dafny.ISequence<RAST._ITypeParamDecl> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1152_typeParamsSeq = _out47;
      _1153_rTypeParams = _out48;
      _1154_rTypeParamsDecls = _out49;
      _1155_whereConstraints = _out50;
      Dafny.ISequence<Dafny.Rune> _1156_constrainedTypeParams;
      _1156_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1154_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1157_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source52 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched52 = true;
      if (unmatched52) {
        if (_source52.is_Some) {
          RAST._IType _1158_v = _source52.dtor_value;
          unmatched52 = false;
          _1157_underlyingType = _1158_v;
        }
      }
      if (unmatched52) {
        unmatched52 = false;
        RAST._IType _out51;
        _out51 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1157_underlyingType = _out51;
      }
      DAST._IType _1159_resultingType;
      _1159_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1160_newtypeName;
      _1160_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1160_newtypeName, _1154_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1157_underlyingType))))));
      RAST._IExpr _1161_fnBody;
      _1161_fnBody = RAST.Expr.create_Identifier(_1160_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source53 = (c).dtor_witnessExpr;
      bool unmatched53 = true;
      if (unmatched53) {
        if (_source53.is_Some) {
          DAST._IExpression _1162_e = _source53.dtor_value;
          unmatched53 = false;
          {
            DAST._IExpression _1163_e;
            _1163_e = ((object.Equals((c).dtor_base, _1159_resultingType)) ? (_1162_e) : (DAST.Expression.create_Convert(_1162_e, (c).dtor_base, _1159_resultingType)));
            RAST._IExpr _1164_eStr;
            DCOMP._IOwnership _1165___v53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1166___v54;
            RAST._IExpr _out52;
            DCOMP._IOwnership _out53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out54;
            (this).GenExpr(_1163_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out52, out _out53, out _out54);
            _1164_eStr = _out52;
            _1165___v53 = _out53;
            _1166___v54 = _out54;
            _1161_fnBody = (_1161_fnBody).Apply1(_1164_eStr);
          }
        }
      }
      if (unmatched53) {
        unmatched53 = false;
        {
          _1161_fnBody = (_1161_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1167_body;
      _1167_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1161_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source54 = (c).dtor_constraint;
      bool unmatched54 = true;
      if (unmatched54) {
        if (_source54.is_None) {
          unmatched54 = false;
        }
      }
      if (unmatched54) {
        DAST._INewtypeConstraint value8 = _source54.dtor_value;
        DAST._IFormal _1168_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1169_constraintStmts = value8.dtor_constraintStmts;
        unmatched54 = false;
        RAST._IExpr _1170_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1171___v55;
        DCOMP._IEnvironment _1172_newEnv;
        RAST._IExpr _out55;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out56;
        DCOMP._IEnvironment _out57;
        (this).GenStmts(_1169_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out55, out _out56, out _out57);
        _1170_rStmts = _out55;
        _1171___v55 = _out56;
        _1172_newEnv = _out57;
        Dafny.ISequence<RAST._IFormal> _1173_rFormals;
        Dafny.ISequence<RAST._IFormal> _out58;
        _out58 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1168_formal));
        _1173_rFormals = _out58;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1154_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1160_newtypeName), _1153_rTypeParams), _1155_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1173_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1170_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1154_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1160_newtypeName), _1153_rTypeParams), _1155_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1167_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1154_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1160_newtypeName), _1153_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1154_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1160_newtypeName), _1153_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1157_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1174_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1175_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1176_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1177_whereConstraints;
      Dafny.ISequence<DAST._IType> _out59;
      Dafny.ISequence<RAST._IType> _out60;
      Dafny.ISequence<RAST._ITypeParamDecl> _out61;
      Dafny.ISequence<Dafny.Rune> _out62;
      (this).GenTypeParameters((c).dtor_typeParams, out _out59, out _out60, out _out61, out _out62);
      _1174_typeParamsSeq = _out59;
      _1175_rTypeParams = _out60;
      _1176_rTypeParamsDecls = _out61;
      _1177_whereConstraints = _out62;
      Dafny.ISequence<Dafny.Rune> _1178_constrainedTypeParams;
      _1178_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1176_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _1179_synonymTypeName;
      _1179_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1180_resultingType;
      RAST._IType _out63;
      _out63 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1180_resultingType = _out63;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1179_synonymTypeName, _1176_rTypeParamsDecls, _1180_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source55 = (c).dtor_witnessExpr;
      bool unmatched55 = true;
      if (unmatched55) {
        if (_source55.is_Some) {
          DAST._IExpression _1181_e = _source55.dtor_value;
          unmatched55 = false;
          {
            RAST._IExpr _1182_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1183___v56;
            DCOMP._IEnvironment _1184_newEnv;
            RAST._IExpr _out64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out65;
            DCOMP._IEnvironment _out66;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out64, out _out65, out _out66);
            _1182_rStmts = _out64;
            _1183___v56 = _out65;
            _1184_newEnv = _out66;
            RAST._IExpr _1185_rExpr;
            DCOMP._IOwnership _1186___v57;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1187___v58;
            RAST._IExpr _out67;
            DCOMP._IOwnership _out68;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out69;
            (this).GenExpr(_1181_e, DCOMP.SelfInfo.create_NoSelf(), _1184_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out67, out _out68, out _out69);
            _1185_rExpr = _out67;
            _1186___v57 = _out68;
            _1187___v58 = _out69;
            Dafny.ISequence<Dafny.Rune> _1188_constantName;
            _1188_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1188_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1180_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1182_rStmts).Then(_1185_rExpr)))))));
          }
        }
      }
      if (unmatched55) {
        unmatched55 = false;
      }
      return s;
    }
    public bool TypeIsEq(DAST._IType t) {
      DAST._IType _source56 = t;
      bool unmatched56 = true;
      if (unmatched56) {
        if (_source56.is_UserDefined) {
          DAST._IResolvedType _1189___v59 = _source56.dtor_resolved;
          unmatched56 = false;
          return true;
        }
      }
      if (unmatched56) {
        if (_source56.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1190_ts = _source56.dtor_Tuple_a0;
          unmatched56 = false;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1191_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1191_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1192_t = (DAST._IType)_forall_var_5;
            return !((_1191_ts).Contains(_1192_t)) || ((this).TypeIsEq(_1192_t));
          }))))(_1190_ts);
        }
      }
      if (unmatched56) {
        if (_source56.is_Array) {
          DAST._IType _1193_t = _source56.dtor_element;
          BigInteger _1194___v60 = _source56.dtor_dims;
          unmatched56 = false;
          return (this).TypeIsEq(_1193_t);
        }
      }
      if (unmatched56) {
        if (_source56.is_Seq) {
          DAST._IType _1195_t = _source56.dtor_element;
          unmatched56 = false;
          return (this).TypeIsEq(_1195_t);
        }
      }
      if (unmatched56) {
        if (_source56.is_Set) {
          DAST._IType _1196_t = _source56.dtor_element;
          unmatched56 = false;
          return (this).TypeIsEq(_1196_t);
        }
      }
      if (unmatched56) {
        if (_source56.is_Multiset) {
          DAST._IType _1197_t = _source56.dtor_element;
          unmatched56 = false;
          return (this).TypeIsEq(_1197_t);
        }
      }
      if (unmatched56) {
        if (_source56.is_Map) {
          DAST._IType _1198_k = _source56.dtor_key;
          DAST._IType _1199_v = _source56.dtor_value;
          unmatched56 = false;
          return ((this).TypeIsEq(_1198_k)) && ((this).TypeIsEq(_1199_v));
        }
      }
      if (unmatched56) {
        if (_source56.is_SetBuilder) {
          DAST._IType _1200_t = _source56.dtor_element;
          unmatched56 = false;
          return (this).TypeIsEq(_1200_t);
        }
      }
      if (unmatched56) {
        if (_source56.is_MapBuilder) {
          DAST._IType _1201_k = _source56.dtor_key;
          DAST._IType _1202_v = _source56.dtor_value;
          unmatched56 = false;
          return ((this).TypeIsEq(_1201_k)) && ((this).TypeIsEq(_1202_v));
        }
      }
      if (unmatched56) {
        if (_source56.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1203___v61 = _source56.dtor_args;
          DAST._IType _1204___v62 = _source56.dtor_result;
          unmatched56 = false;
          return false;
        }
      }
      if (unmatched56) {
        if (_source56.is_Primitive) {
          DAST._IPrimitive _1205___v63 = _source56.dtor_Primitive_a0;
          unmatched56 = false;
          return true;
        }
      }
      if (unmatched56) {
        if (_source56.is_Passthrough) {
          Dafny.ISequence<Dafny.Rune> _1206___v64 = _source56.dtor_Passthrough_a0;
          unmatched56 = false;
          return true;
        }
      }
      if (unmatched56) {
        if (_source56.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _1207_i = _source56.dtor_TypeArg_a0;
          unmatched56 = false;
          return true;
        }
      }
      if (unmatched56) {
        unmatched56 = false;
        return true;
      }
      throw new System.Exception("unexpected control point");
    }
    public bool DatatypeIsEq(DAST._IDatatype c) {
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1208_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1208_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1209_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1209_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1210_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1208_c).dtor_ctors).Contains(_1209_ctor)) && (((_1209_ctor).dtor_args).Contains(_1210_arg))) || ((this).TypeIsEq(((_1210_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1211_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1212_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1213_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1214_whereConstraints;
      Dafny.ISequence<DAST._IType> _out70;
      Dafny.ISequence<RAST._IType> _out71;
      Dafny.ISequence<RAST._ITypeParamDecl> _out72;
      Dafny.ISequence<Dafny.Rune> _out73;
      (this).GenTypeParameters((c).dtor_typeParams, out _out70, out _out71, out _out72, out _out73);
      _1211_typeParamsSeq = _out70;
      _1212_rTypeParams = _out71;
      _1213_rTypeParamsDecls = _out72;
      _1214_whereConstraints = _out73;
      Dafny.ISequence<Dafny.Rune> _1215_datatypeName;
      _1215_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1216_ctors;
      _1216_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi12 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1217_i = BigInteger.Zero; _1217_i < _hi12; _1217_i++) {
        DAST._IDatatypeCtor _1218_ctor;
        _1218_ctor = ((c).dtor_ctors).Select(_1217_i);
        Dafny.ISequence<RAST._IField> _1219_ctorArgs;
        _1219_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1220_isNumeric;
        _1220_isNumeric = false;
        BigInteger _hi13 = new BigInteger(((_1218_ctor).dtor_args).Count);
        for (BigInteger _1221_j = BigInteger.Zero; _1221_j < _hi13; _1221_j++) {
          DAST._IDatatypeDtor _1222_dtor;
          _1222_dtor = ((_1218_ctor).dtor_args).Select(_1221_j);
          RAST._IType _1223_formalType;
          RAST._IType _out74;
          _out74 = (this).GenType(((_1222_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1223_formalType = _out74;
          Dafny.ISequence<Dafny.Rune> _1224_formalName;
          _1224_formalName = DCOMP.__default.escapeName(((_1222_dtor).dtor_formal).dtor_name);
          if (((_1221_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1224_formalName))) {
            _1220_isNumeric = true;
          }
          if ((((_1221_j).Sign != 0) && (_1220_isNumeric)) && (!(Std.Strings.__default.OfNat(_1221_j)).Equals(_1224_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1224_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1221_j)));
            _1220_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1219_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1219_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1224_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1223_formalType))))));
          } else {
            _1219_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1219_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1224_formalName, _1223_formalType))));
          }
        }
        RAST._IFields _1225_namedFields;
        _1225_namedFields = RAST.Fields.create_NamedFields(_1219_ctorArgs);
        if (_1220_isNumeric) {
          _1225_namedFields = (_1225_namedFields).ToNamelessFields();
        }
        _1216_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1216_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1218_ctor).dtor_name), _1225_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1226_selfPath;
      _1226_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1227_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1228_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out75;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out76;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1226_selfPath, _1211_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1211_typeParamsSeq, out _out75, out _out76);
      _1227_implBodyRaw = _out75;
      _1228_traitBodies = _out76;
      Dafny.ISequence<RAST._IImplMember> _1229_implBody;
      _1229_implBody = _1227_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1230_emittedFields;
      _1230_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi14 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1231_i = BigInteger.Zero; _1231_i < _hi14; _1231_i++) {
        DAST._IDatatypeCtor _1232_ctor;
        _1232_ctor = ((c).dtor_ctors).Select(_1231_i);
        BigInteger _hi15 = new BigInteger(((_1232_ctor).dtor_args).Count);
        for (BigInteger _1233_j = BigInteger.Zero; _1233_j < _hi15; _1233_j++) {
          DAST._IDatatypeDtor _1234_dtor;
          _1234_dtor = ((_1232_ctor).dtor_args).Select(_1233_j);
          Dafny.ISequence<Dafny.Rune> _1235_callName;
          _1235_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1234_dtor).dtor_callName, DCOMP.__default.escapeName(((_1234_dtor).dtor_formal).dtor_name));
          if (!((_1230_emittedFields).Contains(_1235_callName))) {
            _1230_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1230_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1235_callName));
            RAST._IType _1236_formalType;
            RAST._IType _out77;
            _out77 = (this).GenType(((_1234_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1236_formalType = _out77;
            Dafny.ISequence<RAST._IMatchCase> _1237_cases;
            _1237_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1238_k = BigInteger.Zero; _1238_k < _hi16; _1238_k++) {
              DAST._IDatatypeCtor _1239_ctor2;
              _1239_ctor2 = ((c).dtor_ctors).Select(_1238_k);
              Dafny.ISequence<Dafny.Rune> _1240_pattern;
              _1240_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1215_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1239_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1241_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1242_hasMatchingField;
              _1242_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1243_patternInner;
              _1243_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1244_isNumeric;
              _1244_isNumeric = false;
              BigInteger _hi17 = new BigInteger(((_1239_ctor2).dtor_args).Count);
              for (BigInteger _1245_l = BigInteger.Zero; _1245_l < _hi17; _1245_l++) {
                DAST._IDatatypeDtor _1246_dtor2;
                _1246_dtor2 = ((_1239_ctor2).dtor_args).Select(_1245_l);
                Dafny.ISequence<Dafny.Rune> _1247_patternName;
                _1247_patternName = DCOMP.__default.escapeDtor(((_1246_dtor2).dtor_formal).dtor_name);
                if (((_1245_l).Sign == 0) && ((_1247_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1244_isNumeric = true;
                }
                if (_1244_isNumeric) {
                  _1247_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1246_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1245_l)));
                }
                if (object.Equals(((_1234_dtor).dtor_formal).dtor_name, ((_1246_dtor2).dtor_formal).dtor_name)) {
                  _1242_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1247_patternName);
                }
                _1243_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1243_patternInner, _1247_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1244_isNumeric) {
                _1240_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1240_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1243_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1240_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1240_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1243_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1242_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1241_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1242_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1241_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1242_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1241_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1248_ctorMatch;
              _1248_ctorMatch = RAST.MatchCase.create(_1240_pattern, RAST.Expr.create_RawExpr(_1241_rhs));
              _1237_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1237_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1248_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1237_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1237_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1215_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1249_methodBody;
            _1249_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1237_cases);
            _1229_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1229_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1235_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1236_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1249_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1250_types;
        _1250_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi18 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1251_typeI = BigInteger.Zero; _1251_typeI < _hi18; _1251_typeI++) {
          DAST._IType _1252_typeArg;
          RAST._ITypeParamDecl _1253_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_1251_typeI), out _out78, out _out79);
          _1252_typeArg = _out78;
          _1253_rTypeParamDecl = _out79;
          RAST._IType _1254_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1252_typeArg, DCOMP.GenTypeContext.@default());
          _1254_rTypeArg = _out80;
          _1250_types = Dafny.Sequence<RAST._IType>.Concat(_1250_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1254_rTypeArg))));
        }
        _1216_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1216_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1255_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1255_tpe);
})), _1250_types)))));
      }
      bool _1256_cIsEq;
      _1256_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1256_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1215_datatypeName, _1213_rTypeParamsDecls, _1216_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1213_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1215_datatypeName), _1212_rTypeParams), _1214_whereConstraints, _1229_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1257_printImplBodyCases;
      _1257_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1258_hashImplBodyCases;
      _1258_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi19 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1259_i = BigInteger.Zero; _1259_i < _hi19; _1259_i++) {
        DAST._IDatatypeCtor _1260_ctor;
        _1260_ctor = ((c).dtor_ctors).Select(_1259_i);
        Dafny.ISequence<Dafny.Rune> _1261_ctorMatch;
        _1261_ctorMatch = DCOMP.__default.escapeName((_1260_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1262_modulePrefix;
        _1262_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1263_ctorName;
        _1263_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1262_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1260_ctor).dtor_name));
        if (((new BigInteger((_1263_ctorName).Count)) >= (new BigInteger(13))) && (((_1263_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1263_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1264_printRhs;
        _1264_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1263_ctorName), (((_1260_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1265_hashRhs;
        _1265_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        bool _1266_isNumeric;
        _1266_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1267_ctorMatchInner;
        _1267_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi20 = new BigInteger(((_1260_ctor).dtor_args).Count);
        for (BigInteger _1268_j = BigInteger.Zero; _1268_j < _hi20; _1268_j++) {
          DAST._IDatatypeDtor _1269_dtor;
          _1269_dtor = ((_1260_ctor).dtor_args).Select(_1268_j);
          Dafny.ISequence<Dafny.Rune> _1270_patternName;
          _1270_patternName = DCOMP.__default.escapeField(((_1269_dtor).dtor_formal).dtor_name);
          DAST._IType _1271_formalType;
          _1271_formalType = ((_1269_dtor).dtor_formal).dtor_typ;
          if (((_1268_j).Sign == 0) && ((_1270_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1266_isNumeric = true;
          }
          if (_1266_isNumeric) {
            _1270_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1269_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1268_j)));
          }
          _1265_hashRhs = (_1265_hashRhs).Then(((RAST.Expr.create_Identifier(_1270_patternName)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          _1267_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1267_ctorMatchInner, _1270_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1268_j).Sign == 1) {
            _1264_printRhs = (_1264_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1264_printRhs = (_1264_printRhs).Then(RAST.Expr.create_RawExpr((((_1271_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1270_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
        }
        if (_1266_isNumeric) {
          _1261_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1261_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1267_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1261_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1261_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1267_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1260_ctor).dtor_hasAnyArgs) {
          _1264_printRhs = (_1264_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1264_printRhs = (_1264_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1257_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1257_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1215_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1261_ctorMatch), RAST.Expr.create_Block(_1264_printRhs))));
        _1258_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1258_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1215_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1261_ctorMatch), RAST.Expr.create_Block(_1265_hashRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _1257_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1257_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1215_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
        _1258_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1258_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1215_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1272_defaultConstrainedTypeParams;
      _1272_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1213_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1273_rTypeParamsDeclsWithEq;
      _1273_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1213_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1274_rTypeParamsDeclsWithHash;
      _1274_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1213_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1275_printImplBody;
      _1275_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1257_printImplBodyCases);
      RAST._IExpr _1276_hashImplBody;
      _1276_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1258_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1213_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1215_datatypeName), _1212_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1213_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1215_datatypeName), _1212_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1275_printImplBody))))))));
      if (_1256_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1273_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1215_datatypeName), _1212_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1274_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1215_datatypeName), _1212_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1276_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1277_structName;
        _1277_structName = (RAST.Expr.create_Identifier(_1215_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1278_structAssignments;
        _1278_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi21 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1279_i = BigInteger.Zero; _1279_i < _hi21; _1279_i++) {
          DAST._IDatatypeDtor _1280_dtor;
          _1280_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1279_i);
          _1278_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1278_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1280_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1281_defaultConstrainedTypeParams;
        _1281_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1213_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1282_fullType;
        _1282_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1215_datatypeName), _1212_rTypeParams);
        if (_1256_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1281_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1282_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1282_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1277_structName, _1278_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1213_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1282_fullType), RAST.Type.create_Borrowed(_1282_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        BigInteger _hi22 = new BigInteger((p).Count);
        for (BigInteger _1283_i = BigInteger.Zero; _1283_i < _hi22; _1283_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1283_i))));
        }
      }
      return r;
    }
    public static RAST._IExpr GenPathExpr(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> p)
    {
      RAST._IExpr r = RAST.Expr.Default();
      if ((new BigInteger((p).Count)).Sign == 0) {
        r = RAST.__default.self;
        return r;
      } else {
        r = ((((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))) ? (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) : (((((((p).Select(BigInteger.Zero)))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"))) ? (RAST.__default.dafny__runtime) : (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"))))));
        BigInteger _hi23 = new BigInteger((p).Count);
        for (BigInteger _1284_i = BigInteger.Zero; _1284_i < _hi23; _1284_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1284_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi24 = new BigInteger((args).Count);
      for (BigInteger _1285_i = BigInteger.Zero; _1285_i < _hi24; _1285_i++) {
        RAST._IType _1286_genTp;
        RAST._IType _out81;
        _out81 = (this).GenType((args).Select(_1285_i), genTypeContext);
        _1286_genTp = _out81;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1286_genTp));
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, DCOMP._IGenTypeContext genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source57 = c;
      bool unmatched57 = true;
      if (unmatched57) {
        if (_source57.is_UserDefined) {
          DAST._IResolvedType _1287_resolved = _source57.dtor_resolved;
          unmatched57 = false;
          {
            RAST._IType _1288_t;
            RAST._IType _out82;
            _out82 = DCOMP.COMP.GenPath((_1287_resolved).dtor_path);
            _1288_t = _out82;
            Dafny.ISequence<RAST._IType> _1289_typeArgs;
            Dafny.ISequence<RAST._IType> _out83;
            _out83 = (this).GenTypeArgs((_1287_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let9_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let9_0, _1290_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let10_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let10_0, _1291_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1290_dt__update__tmp_h0).dtor_inBinding, (_1290_dt__update__tmp_h0).dtor_inFn, _1291_dt__update_hforTraitParents_h0))))));
            _1289_typeArgs = _out83;
            s = RAST.Type.create_TypeApp(_1288_t, _1289_typeArgs);
            DAST._IResolvedTypeBase _source58 = (_1287_resolved).dtor_kind;
            bool unmatched58 = true;
            if (unmatched58) {
              if (_source58.is_Class) {
                unmatched58 = false;
                {
                  s = (this).Object(s);
                }
              }
            }
            if (unmatched58) {
              if (_source58.is_Datatype) {
                unmatched58 = false;
                {
                  if ((this).IsRcWrapped((_1287_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched58) {
              if (_source58.is_Trait) {
                unmatched58 = false;
                {
                  if (((_1287_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched58) {
              DAST._IType _1292_t = _source58.dtor_baseType;
              DAST._INewtypeRange _1293_range = _source58.dtor_range;
              bool _1294_erased = _source58.dtor_erase;
              unmatched58 = false;
              {
                if (_1294_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source59 = DCOMP.COMP.NewtypeToRustType(_1292_t, _1293_range);
                  bool unmatched59 = true;
                  if (unmatched59) {
                    if (_source59.is_Some) {
                      RAST._IType _1295_v = _source59.dtor_value;
                      unmatched59 = false;
                      s = _1295_v;
                    }
                  }
                  if (unmatched59) {
                    unmatched59 = false;
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_Object) {
          unmatched57 = false;
          {
            s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
            if (!((genTypeContext).dtor_forTraitParents)) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1296_types = _source57.dtor_Tuple_a0;
          unmatched57 = false;
          {
            Dafny.ISequence<RAST._IType> _1297_args;
            _1297_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1298_i;
            _1298_i = BigInteger.Zero;
            while ((_1298_i) < (new BigInteger((_1296_types).Count))) {
              RAST._IType _1299_generated;
              RAST._IType _out84;
              _out84 = (this).GenType((_1296_types).Select(_1298_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _1300_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _1301_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1300_dt__update__tmp_h1).dtor_inBinding, (_1300_dt__update__tmp_h1).dtor_inFn, _1301_dt__update_hforTraitParents_h1))))));
              _1299_generated = _out84;
              _1297_args = Dafny.Sequence<RAST._IType>.Concat(_1297_args, Dafny.Sequence<RAST._IType>.FromElements(_1299_generated));
              _1298_i = (_1298_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1296_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1297_args)) : (RAST.__default.SystemTupleType(_1297_args)));
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_Array) {
          DAST._IType _1302_element = _source57.dtor_element;
          BigInteger _1303_dims = _source57.dtor_dims;
          unmatched57 = false;
          {
            if ((_1303_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1304_elem;
              RAST._IType _out85;
              _out85 = (this).GenType(_1302_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _1305_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _1306_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1305_dt__update__tmp_h2).dtor_inBinding, (_1305_dt__update__tmp_h2).dtor_inFn, _1306_dt__update_hforTraitParents_h2))))));
              _1304_elem = _out85;
              if ((_1303_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1304_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1307_n;
                _1307_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1303_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1307_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1304_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_Seq) {
          DAST._IType _1308_element = _source57.dtor_element;
          unmatched57 = false;
          {
            RAST._IType _1309_elem;
            RAST._IType _out86;
            _out86 = (this).GenType(_1308_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _1310_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _1311_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1310_dt__update__tmp_h3).dtor_inBinding, (_1310_dt__update__tmp_h3).dtor_inFn, _1311_dt__update_hforTraitParents_h3))))));
            _1309_elem = _out86;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1309_elem));
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_Set) {
          DAST._IType _1312_element = _source57.dtor_element;
          unmatched57 = false;
          {
            RAST._IType _1313_elem;
            RAST._IType _out87;
            _out87 = (this).GenType(_1312_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _1314_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _1315_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1314_dt__update__tmp_h4).dtor_inBinding, (_1314_dt__update__tmp_h4).dtor_inFn, _1315_dt__update_hforTraitParents_h4))))));
            _1313_elem = _out87;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1313_elem));
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_Multiset) {
          DAST._IType _1316_element = _source57.dtor_element;
          unmatched57 = false;
          {
            RAST._IType _1317_elem;
            RAST._IType _out88;
            _out88 = (this).GenType(_1316_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _1318_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _1319_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1318_dt__update__tmp_h5).dtor_inBinding, (_1318_dt__update__tmp_h5).dtor_inFn, _1319_dt__update_hforTraitParents_h5))))));
            _1317_elem = _out88;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1317_elem));
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_Map) {
          DAST._IType _1320_key = _source57.dtor_key;
          DAST._IType _1321_value = _source57.dtor_value;
          unmatched57 = false;
          {
            RAST._IType _1322_keyType;
            RAST._IType _out89;
            _out89 = (this).GenType(_1320_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _1323_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _1324_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1323_dt__update__tmp_h6).dtor_inBinding, (_1323_dt__update__tmp_h6).dtor_inFn, _1324_dt__update_hforTraitParents_h6))))));
            _1322_keyType = _out89;
            RAST._IType _1325_valueType;
            RAST._IType _out90;
            _out90 = (this).GenType(_1321_value, genTypeContext);
            _1325_valueType = _out90;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1322_keyType, _1325_valueType));
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_MapBuilder) {
          DAST._IType _1326_key = _source57.dtor_key;
          DAST._IType _1327_value = _source57.dtor_value;
          unmatched57 = false;
          {
            RAST._IType _1328_keyType;
            RAST._IType _out91;
            _out91 = (this).GenType(_1326_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _1329_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _1330_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1329_dt__update__tmp_h7).dtor_inBinding, (_1329_dt__update__tmp_h7).dtor_inFn, _1330_dt__update_hforTraitParents_h7))))));
            _1328_keyType = _out91;
            RAST._IType _1331_valueType;
            RAST._IType _out92;
            _out92 = (this).GenType(_1327_value, genTypeContext);
            _1331_valueType = _out92;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1328_keyType, _1331_valueType));
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_SetBuilder) {
          DAST._IType _1332_elem = _source57.dtor_element;
          unmatched57 = false;
          {
            RAST._IType _1333_elemType;
            RAST._IType _out93;
            _out93 = (this).GenType(_1332_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _1334_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _1335_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1334_dt__update__tmp_h8).dtor_inBinding, (_1334_dt__update__tmp_h8).dtor_inFn, _1335_dt__update_hforTraitParents_h8))))));
            _1333_elemType = _out93;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1333_elemType));
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1336_args = _source57.dtor_args;
          DAST._IType _1337_result = _source57.dtor_result;
          unmatched57 = false;
          {
            Dafny.ISequence<RAST._IType> _1338_argTypes;
            _1338_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1339_i;
            _1339_i = BigInteger.Zero;
            while ((_1339_i) < (new BigInteger((_1336_args).Count))) {
              RAST._IType _1340_generated;
              RAST._IType _out94;
              _out94 = (this).GenType((_1336_args).Select(_1339_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _1341_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _1342_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let29_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let29_0, _1343_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1341_dt__update__tmp_h9).dtor_inBinding, _1343_dt__update_hinFn_h0, _1342_dt__update_hforTraitParents_h9))))))));
              _1340_generated = _out94;
              _1338_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1338_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1340_generated)));
              _1339_i = (_1339_i) + (BigInteger.One);
            }
            RAST._IType _1344_resultType;
            RAST._IType _out95;
            _out95 = (this).GenType(_1337_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1344_resultType = _out95;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1338_argTypes, _1344_resultType)));
          }
        }
      }
      if (unmatched57) {
        if (_source57.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source57.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1345_name = _h90;
          unmatched57 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1345_name));
        }
      }
      if (unmatched57) {
        if (_source57.is_Primitive) {
          DAST._IPrimitive _1346_p = _source57.dtor_Primitive_a0;
          unmatched57 = false;
          {
            DAST._IPrimitive _source60 = _1346_p;
            bool unmatched60 = true;
            if (unmatched60) {
              if (_source60.is_Int) {
                unmatched60 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
              }
            }
            if (unmatched60) {
              if (_source60.is_Real) {
                unmatched60 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
              }
            }
            if (unmatched60) {
              if (_source60.is_String) {
                unmatched60 = false;
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
              }
            }
            if (unmatched60) {
              if (_source60.is_Bool) {
                unmatched60 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched60) {
              unmatched60 = false;
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          }
        }
      }
      if (unmatched57) {
        Dafny.ISequence<Dafny.Rune> _1347_v = _source57.dtor_Passthrough_a0;
        unmatched57 = false;
        s = RAST.__default.RawType(_1347_v);
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
      for (BigInteger _1348_i = BigInteger.Zero; _1348_i < _hi25; _1348_i++) {
        DAST._IMethod _source61 = (body).Select(_1348_i);
        bool unmatched61 = true;
        if (unmatched61) {
          DAST._IMethod _1349_m = _source61;
          unmatched61 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source62 = (_1349_m).dtor_overridingPath;
            bool unmatched62 = true;
            if (unmatched62) {
              if (_source62.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1350_p = _source62.dtor_value;
                unmatched62 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1351_existing;
                  _1351_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1350_p)) {
                    _1351_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1350_p);
                  }
                  if (((new BigInteger(((_1349_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1352_genMethod;
                  RAST._IImplMember _out96;
                  _out96 = (this).GenMethod(_1349_m, true, enclosingType, enclosingTypeParams);
                  _1352_genMethod = _out96;
                  _1351_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1351_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1352_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1350_p, _1351_existing)));
                }
              }
            }
            if (unmatched62) {
              unmatched62 = false;
              {
                RAST._IImplMember _1353_generated;
                RAST._IImplMember _out97;
                _out97 = (this).GenMethod(_1349_m, forTrait, enclosingType, enclosingTypeParams);
                _1353_generated = _out97;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1353_generated));
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
      BigInteger _hi26 = new BigInteger((@params).Count);
      for (BigInteger _1354_i = BigInteger.Zero; _1354_i < _hi26; _1354_i++) {
        DAST._IFormal _1355_param;
        _1355_param = (@params).Select(_1354_i);
        RAST._IType _1356_paramType;
        RAST._IType _out98;
        _out98 = (this).GenType((_1355_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1356_paramType = _out98;
        if ((!((_1356_paramType).CanReadWithoutClone())) && (!((_1355_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1356_paramType = RAST.Type.create_Borrowed(_1356_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1355_param).dtor_name), _1356_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1357_params;
      Dafny.ISequence<RAST._IFormal> _out99;
      _out99 = (this).GenParams((m).dtor_params);
      _1357_params = _out99;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1358_paramNames;
      _1358_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1359_paramTypes;
      _1359_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi27 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1360_paramI = BigInteger.Zero; _1360_paramI < _hi27; _1360_paramI++) {
        DAST._IFormal _1361_dafny__formal;
        _1361_dafny__formal = ((m).dtor_params).Select(_1360_paramI);
        RAST._IFormal _1362_formal;
        _1362_formal = (_1357_params).Select(_1360_paramI);
        Dafny.ISequence<Dafny.Rune> _1363_name;
        _1363_name = (_1362_formal).dtor_name;
        _1358_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1358_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1363_name));
        _1359_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1359_paramTypes, _1363_name, (_1362_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1364_fnName;
      _1364_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1365_selfIdent;
      _1365_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1366_selfId;
        _1366_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_1364_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _1366_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv107 = enclosingTypeParams;
        var _pat_let_tv108 = enclosingType;
        DAST._IType _1367_instanceType;
        _1367_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source63 = enclosingType;
          bool unmatched63 = true;
          if (unmatched63) {
            if (_source63.is_UserDefined) {
              DAST._IResolvedType _1368_r = _source63.dtor_resolved;
              unmatched63 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1368_r, _pat_let30_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let30_0, _1369_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv107, _pat_let31_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let31_0, _1370_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1369_dt__update__tmp_h0).dtor_path, _1370_dt__update_htypeArgs_h0, (_1369_dt__update__tmp_h0).dtor_kind, (_1369_dt__update__tmp_h0).dtor_attributes, (_1369_dt__update__tmp_h0).dtor_properMethods, (_1369_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched63) {
            DAST._IType _1371___v65 = _source63;
            unmatched63 = false;
            return _pat_let_tv108;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1372_selfFormal;
          _1372_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1357_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1372_selfFormal), _1357_params);
        } else {
          RAST._IType _1373_tpe;
          RAST._IType _out100;
          _out100 = (this).GenType(_1367_instanceType, DCOMP.GenTypeContext.@default());
          _1373_tpe = _out100;
          if ((_1366_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1373_tpe = RAST.Type.create_Borrowed(_1373_tpe);
          } else if ((_1366_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1373_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1373_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1373_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              _1373_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.Type.create_SelfOwned()));
            }
          }
          _1357_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1366_selfId, _1373_tpe)), _1357_params);
        }
        _1365_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1366_selfId, _1367_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1374_retTypeArgs;
      _1374_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1375_typeI;
      _1375_typeI = BigInteger.Zero;
      while ((_1375_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1376_typeExpr;
        RAST._IType _out101;
        _out101 = (this).GenType(((m).dtor_outTypes).Select(_1375_typeI), DCOMP.GenTypeContext.@default());
        _1376_typeExpr = _out101;
        _1374_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1374_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1376_typeExpr));
        _1375_typeI = (_1375_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1377_visibility;
      _1377_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1378_typeParamsFiltered;
      _1378_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1379_typeParamI = BigInteger.Zero; _1379_typeParamI < _hi28; _1379_typeParamI++) {
        DAST._ITypeArgDecl _1380_typeParam;
        _1380_typeParam = ((m).dtor_typeParams).Select(_1379_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1380_typeParam).dtor_name)))) {
          _1378_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1378_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1380_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1381_typeParams;
      _1381_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1378_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi29 = new BigInteger((_1378_typeParamsFiltered).Count);
        for (BigInteger _1382_i = BigInteger.Zero; _1382_i < _hi29; _1382_i++) {
          DAST._IType _1383_typeArg;
          RAST._ITypeParamDecl _1384_rTypeParamDecl;
          DAST._IType _out102;
          RAST._ITypeParamDecl _out103;
          (this).GenTypeParam((_1378_typeParamsFiltered).Select(_1382_i), out _out102, out _out103);
          _1383_typeArg = _out102;
          _1384_rTypeParamDecl = _out103;
          var _pat_let_tv109 = _1384_rTypeParamDecl;
          _1384_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1384_rTypeParamDecl, _pat_let32_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let32_0, _1385_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv109).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let33_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let33_0, _1386_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1385_dt__update__tmp_h1).dtor_content, _1386_dt__update_hconstraints_h0)))));
          _1381_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1381_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1384_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1387_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1388_env = DCOMP.Environment.Default();
      RAST._IExpr _1389_preBody;
      _1389_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1390_preAssignNames;
      _1390_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1391_preAssignTypes;
      _1391_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        RAST._IExpr _1392_earlyReturn;
        _1392_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source64 = (m).dtor_outVars;
        bool unmatched64 = true;
        if (unmatched64) {
          if (_source64.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1393_outVars = _source64.dtor_value;
            unmatched64 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1392_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(Dafny.Sequence<RAST._IExpr>.FromElements())));
                BigInteger _hi30 = new BigInteger((_1393_outVars).Count);
                for (BigInteger _1394_outI = BigInteger.Zero; _1394_outI < _hi30; _1394_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1395_outVar;
                  _1395_outVar = (_1393_outVars).Select(_1394_outI);
                  Dafny.ISequence<Dafny.Rune> _1396_outName;
                  _1396_outName = DCOMP.__default.escapeName((_1395_outVar));
                  Dafny.ISequence<Dafny.Rune> _1397_tracker__name;
                  _1397_tracker__name = DCOMP.__default.AddAssignedPrefix(_1396_outName);
                  _1390_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1390_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1397_tracker__name));
                  _1391_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1391_preAssignTypes, _1397_tracker__name, RAST.Type.create_Bool());
                  _1389_preBody = (_1389_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1397_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<RAST._IExpr> _1398_tupleArgs;
                _1398_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
                BigInteger _hi31 = new BigInteger((_1393_outVars).Count);
                for (BigInteger _1399_outI = BigInteger.Zero; _1399_outI < _hi31; _1399_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1400_outVar;
                  _1400_outVar = (_1393_outVars).Select(_1399_outI);
                  RAST._IType _1401_outType;
                  RAST._IType _out104;
                  _out104 = (this).GenType(((m).dtor_outTypes).Select(_1399_outI), DCOMP.GenTypeContext.@default());
                  _1401_outType = _out104;
                  Dafny.ISequence<Dafny.Rune> _1402_outName;
                  _1402_outName = DCOMP.__default.escapeName((_1400_outVar));
                  _1358_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1358_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1402_outName));
                  RAST._IType _1403_outMaybeType;
                  _1403_outMaybeType = (((_1401_outType).CanReadWithoutClone()) ? (_1401_outType) : (RAST.__default.MaybePlaceboType(_1401_outType)));
                  _1359_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1359_paramTypes, _1402_outName, _1403_outMaybeType);
                  RAST._IExpr _1404_outVarReturn;
                  DCOMP._IOwnership _1405___v66;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1406___v67;
                  RAST._IExpr _out105;
                  DCOMP._IOwnership _out106;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out107;
                  (this).GenExpr(DAST.Expression.create_Ident((_1400_outVar)), DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1402_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1402_outName, _1403_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out105, out _out106, out _out107);
                  _1404_outVarReturn = _out105;
                  _1405___v66 = _out106;
                  _1406___v67 = _out107;
                  _1398_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1398_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1404_outVarReturn));
                }
                if ((new BigInteger((_1398_tupleArgs).Count)) == (BigInteger.One)) {
                  _1392_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1398_tupleArgs).Select(BigInteger.Zero)));
                } else {
                  _1392_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1398_tupleArgs)));
                }
              }
            }
          }
        }
        if (unmatched64) {
          unmatched64 = false;
        }
        _1388_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1390_preAssignNames, _1358_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1391_preAssignTypes, _1359_paramTypes));
        RAST._IExpr _1407_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1408___v68;
        DCOMP._IEnvironment _1409___v69;
        RAST._IExpr _out108;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out109;
        DCOMP._IEnvironment _out110;
        (this).GenStmts((m).dtor_body, _1365_selfIdent, _1388_env, true, _1392_earlyReturn, out _out108, out _out109, out _out110);
        _1407_body = _out108;
        _1408___v68 = _out109;
        _1409___v69 = _out110;
        _1387_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1389_preBody).Then(_1407_body));
      } else {
        _1388_env = DCOMP.Environment.create(_1358_paramNames, _1359_paramTypes);
        _1387_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1377_visibility, RAST.Fn.create(_1364_fnName, _1381_typeParams, _1357_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1374_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1374_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1374_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1387_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1410_declarations;
      _1410_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1411_i;
      _1411_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1412_stmts;
      _1412_stmts = stmts;
      while ((_1411_i) < (new BigInteger((_1412_stmts).Count))) {
        DAST._IStatement _1413_stmt;
        _1413_stmt = (_1412_stmts).Select(_1411_i);
        DAST._IStatement _source65 = _1413_stmt;
        bool unmatched65 = true;
        if (unmatched65) {
          if (_source65.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1414_name = _source65.dtor_name;
            DAST._IType _1415_optType = _source65.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source65.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched65 = false;
              if (((_1411_i) + (BigInteger.One)) < (new BigInteger((_1412_stmts).Count))) {
                DAST._IStatement _source66 = (_1412_stmts).Select((_1411_i) + (BigInteger.One));
                bool unmatched66 = true;
                if (unmatched66) {
                  if (_source66.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source66.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _1416_name2 = ident0;
                      DAST._IExpression _1417_rhs = _source66.dtor_value;
                      unmatched66 = false;
                      if (object.Equals(_1416_name2, _1414_name)) {
                        _1412_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1412_stmts).Subsequence(BigInteger.Zero, _1411_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1414_name, _1415_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1417_rhs)))), (_1412_stmts).Drop((_1411_i) + (new BigInteger(2))));
                        _1413_stmt = (_1412_stmts).Select(_1411_i);
                      }
                    }
                  }
                }
                if (unmatched66) {
                  DAST._IStatement _1418___v70 = _source66;
                  unmatched66 = false;
                }
              }
            }
          }
        }
        if (unmatched65) {
          DAST._IStatement _1419___v71 = _source65;
          unmatched65 = false;
        }
        RAST._IExpr _1420_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1421_recIdents;
        DCOMP._IEnvironment _1422_newEnv2;
        RAST._IExpr _out111;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
        DCOMP._IEnvironment _out113;
        (this).GenStmt(_1413_stmt, selfIdent, newEnv, (isLast) && ((_1411_i) == ((new BigInteger((_1412_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out111, out _out112, out _out113);
        _1420_stmtExpr = _out111;
        _1421_recIdents = _out112;
        _1422_newEnv2 = _out113;
        newEnv = _1422_newEnv2;
        DAST._IStatement _source67 = _1413_stmt;
        bool unmatched67 = true;
        if (unmatched67) {
          if (_source67.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1423_name = _source67.dtor_name;
            DAST._IType _1424___v72 = _source67.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> _1425___v73 = _source67.dtor_maybeValue;
            unmatched67 = false;
            {
              _1410_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1410_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1423_name)));
            }
          }
        }
        if (unmatched67) {
          DAST._IStatement _1426___v74 = _source67;
          unmatched67 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1421_recIdents, _1410_declarations));
        generated = (generated).Then(_1420_stmtExpr);
        _1411_i = (_1411_i) + (BigInteger.One);
        if ((_1420_stmtExpr).is_Return) {
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
      DAST._IAssignLhs _source68 = lhs;
      bool unmatched68 = true;
      if (unmatched68) {
        if (_source68.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident1 = _source68.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _1427_id = ident1;
          unmatched68 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1428_idRust;
            _1428_idRust = DCOMP.__default.escapeName(_1427_id);
            if (((env).IsBorrowed(_1428_idRust)) || ((env).IsBorrowedMut(_1428_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1428_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1428_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1428_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched68) {
        if (_source68.is_Select) {
          DAST._IExpression _1429_on = _source68.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1430_field = _source68.dtor_field;
          unmatched68 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1431_fieldName;
            _1431_fieldName = DCOMP.__default.escapeName(_1430_field);
            RAST._IExpr _1432_onExpr;
            DCOMP._IOwnership _1433_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1434_recIdents;
            RAST._IExpr _out114;
            DCOMP._IOwnership _out115;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
            (this).GenExpr(_1429_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out114, out _out115, out _out116);
            _1432_onExpr = _out114;
            _1433_onOwned = _out115;
            _1434_recIdents = _out116;
            RAST._IExpr _source69 = _1432_onExpr;
            bool unmatched69 = true;
            if (unmatched69) {
              bool disjunctiveMatch9 = false;
              if (_source69.is_Call) {
                RAST._IExpr obj2 = _source69.dtor_obj;
                if (obj2.is_Select) {
                  RAST._IExpr obj3 = obj2.dtor_obj;
                  if (obj3.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name17 = obj3.dtor_name;
                    if (object.Equals(name17, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      Dafny.ISequence<Dafny.Rune> name18 = obj2.dtor_name;
                      if (object.Equals(name18, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                        Dafny.ISequence<RAST._IExpr> _1435___v75 = _source69.dtor_arguments;
                        disjunctiveMatch9 = true;
                      }
                    }
                  }
                }
              }
              if (_source69.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name19 = _source69.dtor_name;
                if (object.Equals(name19, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch9 = true;
                }
              }
              if (_source69.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op14 = _source69.dtor_op1;
                if (object.Equals(op14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying4 = _source69.dtor_underlying;
                  if (underlying4.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name20 = underlying4.dtor_name;
                    if (object.Equals(name20, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      DAST.Format._IUnaryOpFormat _1436___v76 = _source69.dtor_format;
                      disjunctiveMatch9 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch9) {
                unmatched69 = false;
                Dafny.ISequence<Dafny.Rune> _1437_isAssignedVar;
                _1437_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1431_fieldName);
                if (((newEnv).dtor_names).Contains(_1437_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1431_fieldName), RAST.Expr.create_Identifier(_1437_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1437_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1437_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1431_fieldName, rhs);
                }
              }
            }
            if (unmatched69) {
              RAST._IExpr _1438___v77 = _source69;
              unmatched69 = false;
              if (!object.Equals(_1432_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1432_onExpr = ((this).modify__macro).Apply1(_1432_onExpr);
              }
              generated = RAST.__default.AssignMember(_1432_onExpr, _1431_fieldName, rhs);
            }
            readIdents = _1434_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched68) {
        DAST._IExpression _1439_on = _source68.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1440_indices = _source68.dtor_indices;
        unmatched68 = false;
        {
          RAST._IExpr _1441_onExpr;
          DCOMP._IOwnership _1442_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1443_recIdents;
          RAST._IExpr _out117;
          DCOMP._IOwnership _out118;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
          (this).GenExpr(_1439_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out117, out _out118, out _out119);
          _1441_onExpr = _out117;
          _1442_onOwned = _out118;
          _1443_recIdents = _out119;
          readIdents = _1443_recIdents;
          _1441_onExpr = ((this).modify__macro).Apply1(_1441_onExpr);
          RAST._IExpr _1444_r;
          _1444_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1445_indicesExpr;
          _1445_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_1440_indices).Count);
          for (BigInteger _1446_i = BigInteger.Zero; _1446_i < _hi32; _1446_i++) {
            RAST._IExpr _1447_idx;
            DCOMP._IOwnership _1448___v78;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1449_recIdentsIdx;
            RAST._IExpr _out120;
            DCOMP._IOwnership _out121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out122;
            (this).GenExpr((_1440_indices).Select(_1446_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out120, out _out121, out _out122);
            _1447_idx = _out120;
            _1448___v78 = _out121;
            _1449_recIdentsIdx = _out122;
            Dafny.ISequence<Dafny.Rune> _1450_varName;
            _1450_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1446_i));
            _1445_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1445_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1450_varName)));
            _1444_r = (_1444_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1450_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), (_1447_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1449_recIdentsIdx);
          }
          if ((new BigInteger((_1440_indices).Count)) > (BigInteger.One)) {
            _1441_onExpr = (_1441_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1451_rhs;
          _1451_rhs = rhs;
          var _pat_let_tv110 = env;
          if (((_1441_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1441_onExpr).LhsIdentifierName(), _pat_let34_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let34_0, _1452_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv110).GetType(_1452_name), _pat_let35_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let35_0, _1453_tpe => ((_1453_tpe).is_Some) && (((_1453_tpe).dtor_value).IsUninitArray())))))))) {
            _1451_rhs = RAST.__default.MaybeUninitNew(_1451_rhs);
          }
          generated = (_1444_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1441_onExpr, _1445_indicesExpr)), _1451_rhs));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source70 = stmt;
      bool unmatched70 = true;
      if (unmatched70) {
        if (_source70.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1454_fields = _source70.dtor_fields;
          unmatched70 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi33 = new BigInteger((_1454_fields).Count);
            for (BigInteger _1455_i = BigInteger.Zero; _1455_i < _hi33; _1455_i++) {
              DAST._IFormal _1456_field;
              _1456_field = (_1454_fields).Select(_1455_i);
              Dafny.ISequence<Dafny.Rune> _1457_fieldName;
              _1457_fieldName = DCOMP.__default.escapeName((_1456_field).dtor_name);
              RAST._IType _1458_fieldTyp;
              RAST._IType _out123;
              _out123 = (this).GenType((_1456_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1458_fieldTyp = _out123;
              Dafny.ISequence<Dafny.Rune> _1459_isAssignedVar;
              _1459_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1457_fieldName);
              if (((newEnv).dtor_names).Contains(_1459_isAssignedVar)) {
                RAST._IExpr _1460_rhs;
                DCOMP._IOwnership _1461___v79;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1462___v80;
                RAST._IExpr _out124;
                DCOMP._IOwnership _out125;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1456_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out124, out _out125, out _out126);
                _1460_rhs = _out124;
                _1461___v79 = _out125;
                _1462___v80 = _out126;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1459_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1457_fieldName), RAST.Expr.create_Identifier(_1459_isAssignedVar), _1460_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1459_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1463_name = _source70.dtor_name;
          DAST._IType _1464_typ = _source70.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source70.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1465_expression = maybeValue1.dtor_value;
            unmatched70 = false;
            {
              RAST._IType _1466_tpe;
              RAST._IType _out127;
              _out127 = (this).GenType(_1464_typ, DCOMP.GenTypeContext.InBinding());
              _1466_tpe = _out127;
              Dafny.ISequence<Dafny.Rune> _1467_varName;
              _1467_varName = DCOMP.__default.escapeName(_1463_name);
              bool _1468_hasCopySemantics;
              _1468_hasCopySemantics = (_1466_tpe).CanReadWithoutClone();
              if (((_1465_expression).is_InitializationValue) && (!(_1468_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1467_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1466_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1467_varName, RAST.__default.MaybePlaceboType(_1466_tpe));
              } else {
                RAST._IExpr _1469_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1470_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1465_expression).is_InitializationValue) && ((_1466_tpe).IsObjectOrPointer())) {
                  _1469_expr = (_1466_tpe).ToNullExpr();
                  _1470_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1471_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out128;
                  DCOMP._IOwnership _out129;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
                  (this).GenExpr(_1465_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out128, out _out129, out _out130);
                  _1469_expr = _out128;
                  _1471_exprOwnership = _out129;
                  _1470_recIdents = _out130;
                }
                readIdents = _1470_recIdents;
                _1466_tpe = (((_1465_expression).is_NewUninitArray) ? ((_1466_tpe).TypeAtInitialization()) : (_1466_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1463_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1466_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1469_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1463_name), _1466_tpe);
              }
            }
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1472_name = _source70.dtor_name;
          DAST._IType _1473_typ = _source70.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source70.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched70 = false;
            {
              DAST._IStatement _1474_newStmt;
              _1474_newStmt = DAST.Statement.create_DeclareVar(_1472_name, _1473_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1473_typ)));
              RAST._IExpr _out131;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out132;
              DCOMP._IEnvironment _out133;
              (this).GenStmt(_1474_newStmt, selfIdent, env, isLast, earlyReturn, out _out131, out _out132, out _out133);
              generated = _out131;
              readIdents = _out132;
              newEnv = _out133;
            }
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_Assign) {
          DAST._IAssignLhs _1475_lhs = _source70.dtor_lhs;
          DAST._IExpression _1476_expression = _source70.dtor_value;
          unmatched70 = false;
          {
            RAST._IExpr _1477_exprGen;
            DCOMP._IOwnership _1478___v81;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1479_exprIdents;
            RAST._IExpr _out134;
            DCOMP._IOwnership _out135;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out136;
            (this).GenExpr(_1476_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out134, out _out135, out _out136);
            _1477_exprGen = _out134;
            _1478___v81 = _out135;
            _1479_exprIdents = _out136;
            if ((_1475_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1480_rustId;
              _1480_rustId = DCOMP.__default.escapeName(((_1475_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1481_tpe;
              _1481_tpe = (env).GetType(_1480_rustId);
              if (((_1481_tpe).is_Some) && ((((_1481_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1477_exprGen = RAST.__default.MaybePlacebo(_1477_exprGen);
              }
            }
            RAST._IExpr _1482_lhsGen;
            bool _1483_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1484_recIdents;
            DCOMP._IEnvironment _1485_resEnv;
            RAST._IExpr _out137;
            bool _out138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out139;
            DCOMP._IEnvironment _out140;
            (this).GenAssignLhs(_1475_lhs, _1477_exprGen, selfIdent, env, out _out137, out _out138, out _out139, out _out140);
            _1482_lhsGen = _out137;
            _1483_needsIIFE = _out138;
            _1484_recIdents = _out139;
            _1485_resEnv = _out140;
            generated = _1482_lhsGen;
            newEnv = _1485_resEnv;
            if (_1483_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1484_recIdents, _1479_exprIdents);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_If) {
          DAST._IExpression _1486_cond = _source70.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1487_thnDafny = _source70.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1488_elsDafny = _source70.dtor_els;
          unmatched70 = false;
          {
            RAST._IExpr _1489_cond;
            DCOMP._IOwnership _1490___v82;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1491_recIdents;
            RAST._IExpr _out141;
            DCOMP._IOwnership _out142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
            (this).GenExpr(_1486_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out141, out _out142, out _out143);
            _1489_cond = _out141;
            _1490___v82 = _out142;
            _1491_recIdents = _out143;
            Dafny.ISequence<Dafny.Rune> _1492_condString;
            _1492_condString = (_1489_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1491_recIdents;
            RAST._IExpr _1493_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1494_thnIdents;
            DCOMP._IEnvironment _1495_thnEnv;
            RAST._IExpr _out144;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out145;
            DCOMP._IEnvironment _out146;
            (this).GenStmts(_1487_thnDafny, selfIdent, env, isLast, earlyReturn, out _out144, out _out145, out _out146);
            _1493_thn = _out144;
            _1494_thnIdents = _out145;
            _1495_thnEnv = _out146;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1494_thnIdents);
            RAST._IExpr _1496_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1497_elsIdents;
            DCOMP._IEnvironment _1498_elsEnv;
            RAST._IExpr _out147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
            DCOMP._IEnvironment _out149;
            (this).GenStmts(_1488_elsDafny, selfIdent, env, isLast, earlyReturn, out _out147, out _out148, out _out149);
            _1496_els = _out147;
            _1497_elsIdents = _out148;
            _1498_elsEnv = _out149;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1497_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1489_cond, _1493_thn, _1496_els);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1499_lbl = _source70.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1500_body = _source70.dtor_body;
          unmatched70 = false;
          {
            RAST._IExpr _1501_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1502_bodyIdents;
            DCOMP._IEnvironment _1503_env2;
            RAST._IExpr _out150;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out151;
            DCOMP._IEnvironment _out152;
            (this).GenStmts(_1500_body, selfIdent, env, isLast, earlyReturn, out _out150, out _out151, out _out152);
            _1501_body = _out150;
            _1502_bodyIdents = _out151;
            _1503_env2 = _out152;
            readIdents = _1502_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1499_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1501_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_While) {
          DAST._IExpression _1504_cond = _source70.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1505_body = _source70.dtor_body;
          unmatched70 = false;
          {
            RAST._IExpr _1506_cond;
            DCOMP._IOwnership _1507___v83;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1508_recIdents;
            RAST._IExpr _out153;
            DCOMP._IOwnership _out154;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out155;
            (this).GenExpr(_1504_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out153, out _out154, out _out155);
            _1506_cond = _out153;
            _1507___v83 = _out154;
            _1508_recIdents = _out155;
            readIdents = _1508_recIdents;
            RAST._IExpr _1509_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1510_bodyIdents;
            DCOMP._IEnvironment _1511_bodyEnv;
            RAST._IExpr _out156;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out157;
            DCOMP._IEnvironment _out158;
            (this).GenStmts(_1505_body, selfIdent, env, false, earlyReturn, out _out156, out _out157, out _out158);
            _1509_bodyExpr = _out156;
            _1510_bodyIdents = _out157;
            _1511_bodyEnv = _out158;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1510_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1506_cond), _1509_bodyExpr);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1512_boundName = _source70.dtor_boundName;
          DAST._IType _1513_boundType = _source70.dtor_boundType;
          DAST._IExpression _1514_overExpr = _source70.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1515_body = _source70.dtor_body;
          unmatched70 = false;
          {
            RAST._IExpr _1516_over;
            DCOMP._IOwnership _1517___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1518_recIdents;
            RAST._IExpr _out159;
            DCOMP._IOwnership _out160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out161;
            (this).GenExpr(_1514_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out159, out _out160, out _out161);
            _1516_over = _out159;
            _1517___v84 = _out160;
            _1518_recIdents = _out161;
            if (((_1514_overExpr).is_MapBoundedPool) || ((_1514_overExpr).is_SetBoundedPool)) {
              _1516_over = ((_1516_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1519_boundTpe;
            RAST._IType _out162;
            _out162 = (this).GenType(_1513_boundType, DCOMP.GenTypeContext.@default());
            _1519_boundTpe = _out162;
            readIdents = _1518_recIdents;
            Dafny.ISequence<Dafny.Rune> _1520_boundRName;
            _1520_boundRName = DCOMP.__default.escapeName(_1512_boundName);
            RAST._IExpr _1521_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1522_bodyIdents;
            DCOMP._IEnvironment _1523_bodyEnv;
            RAST._IExpr _out163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out164;
            DCOMP._IEnvironment _out165;
            (this).GenStmts(_1515_body, selfIdent, (env).AddAssigned(_1520_boundRName, _1519_boundTpe), false, earlyReturn, out _out163, out _out164, out _out165);
            _1521_bodyExpr = _out163;
            _1522_bodyIdents = _out164;
            _1523_bodyEnv = _out165;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1522_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1520_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1520_boundRName, _1516_over, _1521_bodyExpr);
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1524_toLabel = _source70.dtor_toLabel;
          unmatched70 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source71 = _1524_toLabel;
            bool unmatched71 = true;
            if (unmatched71) {
              if (_source71.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1525_lbl = _source71.dtor_value;
                unmatched71 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1525_lbl)));
                }
              }
            }
            if (unmatched71) {
              unmatched71 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1526_body = _source70.dtor_body;
          unmatched70 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1527_selfClone;
              DCOMP._IOwnership _1528___v85;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1529___v86;
              RAST._IExpr _out166;
              DCOMP._IOwnership _out167;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out168;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out166, out _out167, out _out168);
              _1527_selfClone = _out166;
              _1528___v85 = _out167;
              _1529___v86 = _out168;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1527_selfClone)));
            }
            newEnv = env;
            BigInteger _hi34 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1530_paramI = BigInteger.Zero; _1530_paramI < _hi34; _1530_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1531_param;
              _1531_param = ((env).dtor_names).Select(_1530_paramI);
              RAST._IExpr _1532_paramInit;
              DCOMP._IOwnership _1533___v87;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1534___v88;
              RAST._IExpr _out169;
              DCOMP._IOwnership _out170;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out171;
              (this).GenIdent(_1531_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out169, out _out170, out _out171);
              _1532_paramInit = _out169;
              _1533___v87 = _out170;
              _1534___v88 = _out171;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1531_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1532_paramInit)));
              if (((env).dtor_types).Contains(_1531_param)) {
                RAST._IType _1535_declaredType;
                _1535_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1531_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1531_param, _1535_declaredType);
              }
            }
            RAST._IExpr _1536_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1537_bodyIdents;
            DCOMP._IEnvironment _1538_bodyEnv;
            RAST._IExpr _out172;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
            DCOMP._IEnvironment _out174;
            (this).GenStmts(_1526_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out172, out _out173, out _out174);
            _1536_bodyExpr = _out172;
            _1537_bodyIdents = _out173;
            _1538_bodyEnv = _out174;
            readIdents = _1537_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1536_bodyExpr)));
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_JumpTailCallStart) {
          unmatched70 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_Call) {
          DAST._IExpression _1539_on = _source70.dtor_on;
          DAST._ICallName _1540_name = _source70.dtor_callName;
          Dafny.ISequence<DAST._IType> _1541_typeArgs = _source70.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1542_args = _source70.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1543_maybeOutVars = _source70.dtor_outs;
          unmatched70 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1544_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1545_recIdents;
            Dafny.ISequence<RAST._IType> _1546_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1547_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out175;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out176;
            Dafny.ISequence<RAST._IType> _out177;
            Std.Wrappers._IOption<DAST._IResolvedType> _out178;
            (this).GenArgs(selfIdent, _1540_name, _1541_typeArgs, _1542_args, env, out _out175, out _out176, out _out177, out _out178);
            _1544_argExprs = _out175;
            _1545_recIdents = _out176;
            _1546_typeExprs = _out177;
            _1547_fullNameQualifier = _out178;
            readIdents = _1545_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source72 = _1547_fullNameQualifier;
            bool unmatched72 = true;
            if (unmatched72) {
              if (_source72.is_Some) {
                DAST._IResolvedType value9 = _source72.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1548_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1549_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1550_base = value9.dtor_kind;
                Dafny.ISequence<DAST._IAttribute> _1551___v89 = value9.dtor_attributes;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1552___v90 = value9.dtor_properMethods;
                Dafny.ISequence<DAST._IType> _1553___v91 = value9.dtor_extendedTypes;
                unmatched72 = false;
                RAST._IExpr _1554_fullPath;
                RAST._IExpr _out179;
                _out179 = DCOMP.COMP.GenPathExpr(_1548_path);
                _1554_fullPath = _out179;
                Dafny.ISequence<RAST._IType> _1555_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out180;
                _out180 = (this).GenTypeArgs(_1549_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1555_onTypeExprs = _out180;
                RAST._IExpr _1556_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1557_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1558_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1550_base).is_Trait) || ((_1550_base).is_Class)) {
                  RAST._IExpr _out181;
                  DCOMP._IOwnership _out182;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out183;
                  (this).GenExpr(_1539_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out181, out _out182, out _out183);
                  _1556_onExpr = _out181;
                  _1557_recOwnership = _out182;
                  _1558_recIdents = _out183;
                  _1556_onExpr = ((this).modify__macro).Apply1(_1556_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1558_recIdents);
                } else {
                  RAST._IExpr _out184;
                  DCOMP._IOwnership _out185;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out186;
                  (this).GenExpr(_1539_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out184, out _out185, out _out186);
                  _1556_onExpr = _out184;
                  _1557_recOwnership = _out185;
                  _1558_recIdents = _out186;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1558_recIdents);
                }
                generated = ((((_1554_fullPath).ApplyType(_1555_onTypeExprs)).MSel(DCOMP.__default.escapeName((_1540_name).dtor_name))).ApplyType(_1546_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1556_onExpr), _1544_argExprs));
              }
            }
            if (unmatched72) {
              Std.Wrappers._IOption<DAST._IResolvedType> _1559___v92 = _source72;
              unmatched72 = false;
              RAST._IExpr _1560_onExpr;
              DCOMP._IOwnership _1561___v93;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1562_enclosingIdents;
              RAST._IExpr _out187;
              DCOMP._IOwnership _out188;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out189;
              (this).GenExpr(_1539_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out187, out _out188, out _out189);
              _1560_onExpr = _out187;
              _1561___v93 = _out188;
              _1562_enclosingIdents = _out189;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1562_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1563_renderedName;
              _1563_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
                DAST._ICallName _source73 = _1540_name;
                bool unmatched73 = true;
                if (unmatched73) {
                  if (_source73.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _1564_name = _source73.dtor_name;
                    Std.Wrappers._IOption<DAST._IType> _1565___v94 = _source73.dtor_onType;
                    Std.Wrappers._IOption<DAST._IFormal> _1566___v95 = _source73.dtor_receiverArgs;
                    Dafny.ISequence<DAST._IFormal> _1567___v96 = _source73.dtor_signature;
                    unmatched73 = false;
                    return DCOMP.__default.escapeName(_1564_name);
                  }
                }
                if (unmatched73) {
                  bool disjunctiveMatch10 = false;
                  if (_source73.is_MapBuilderAdd) {
                    disjunctiveMatch10 = true;
                  }
                  if (_source73.is_SetBuilderAdd) {
                    disjunctiveMatch10 = true;
                  }
                  if (disjunctiveMatch10) {
                    unmatched73 = false;
                    return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  }
                }
                if (unmatched73) {
                  bool disjunctiveMatch11 = false;
                  disjunctiveMatch11 = true;
                  disjunctiveMatch11 = true;
                  if (disjunctiveMatch11) {
                    unmatched73 = false;
                    return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                  }
                }
                throw new System.Exception("unexpected control point");
              }))();
              DAST._IExpression _source74 = _1539_on;
              bool unmatched74 = true;
              if (unmatched74) {
                if (_source74.is_Companion) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1568___v97 = _source74.dtor_Companion_a0;
                  Dafny.ISequence<DAST._IType> _1569___v98 = _source74.dtor_typeArgs;
                  unmatched74 = false;
                  {
                    _1560_onExpr = (_1560_onExpr).MSel(_1563_renderedName);
                  }
                }
              }
              if (unmatched74) {
                DAST._IExpression _1570___v99 = _source74;
                unmatched74 = false;
                {
                  if (!object.Equals(_1560_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source75 = _1540_name;
                    bool unmatched75 = true;
                    if (unmatched75) {
                      if (_source75.is_CallName) {
                        Dafny.ISequence<Dafny.Rune> _1571___v100 = _source75.dtor_name;
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source75.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1572_tpe = onType0.dtor_value;
                          Std.Wrappers._IOption<DAST._IFormal> _1573___v101 = _source75.dtor_receiverArgs;
                          Dafny.ISequence<DAST._IFormal> _1574___v102 = _source75.dtor_signature;
                          unmatched75 = false;
                          RAST._IType _1575_typ;
                          RAST._IType _out190;
                          _out190 = (this).GenType(_1572_tpe, DCOMP.GenTypeContext.@default());
                          _1575_typ = _out190;
                          if (((_1575_typ).IsObjectOrPointer()) && (!object.Equals(_1560_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1560_onExpr = ((this).modify__macro).Apply1(_1560_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched75) {
                      DAST._ICallName _1576___v103 = _source75;
                      unmatched75 = false;
                    }
                  }
                  _1560_onExpr = (_1560_onExpr).Sel(_1563_renderedName);
                }
              }
              generated = ((_1560_onExpr).ApplyType(_1546_typeExprs)).Apply(_1544_argExprs);
            }
            if (((_1543_maybeOutVars).is_Some) && ((new BigInteger(((_1543_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1577_outVar;
              _1577_outVar = DCOMP.__default.escapeName((((_1543_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1577_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1577_outVar, generated);
            } else if (((_1543_maybeOutVars).is_None) || ((new BigInteger(((_1543_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1578_tmpVar;
              _1578_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1579_tmpId;
              _1579_tmpId = RAST.Expr.create_Identifier(_1578_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1578_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1580_outVars;
              _1580_outVars = (_1543_maybeOutVars).dtor_value;
              BigInteger _hi35 = new BigInteger((_1580_outVars).Count);
              for (BigInteger _1581_outI = BigInteger.Zero; _1581_outI < _hi35; _1581_outI++) {
                Dafny.ISequence<Dafny.Rune> _1582_outVar;
                _1582_outVar = DCOMP.__default.escapeName(((_1580_outVars).Select(_1581_outI)));
                RAST._IExpr _1583_rhs;
                _1583_rhs = (_1579_tmpId).Sel(Std.Strings.__default.OfNat(_1581_outI));
                if (!((env).CanReadWithoutClone(_1582_outVar))) {
                  _1583_rhs = RAST.__default.MaybePlacebo(_1583_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1582_outVar, _1583_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_Return) {
          DAST._IExpression _1584_exprDafny = _source70.dtor_expr;
          unmatched70 = false;
          {
            RAST._IExpr _1585_expr;
            DCOMP._IOwnership _1586___v104;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1587_recIdents;
            RAST._IExpr _out191;
            DCOMP._IOwnership _out192;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
            (this).GenExpr(_1584_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out191, out _out192, out _out193);
            _1585_expr = _out191;
            _1586___v104 = _out192;
            _1587_recIdents = _out193;
            readIdents = _1587_recIdents;
            if (isLast) {
              generated = _1585_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1585_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_EarlyReturn) {
          unmatched70 = false;
          {
            generated = earlyReturn;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched70) {
        if (_source70.is_Halt) {
          unmatched70 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched70) {
        DAST._IExpression _1588_e = _source70.dtor_Print_a0;
        unmatched70 = false;
        {
          RAST._IExpr _1589_printedExpr;
          DCOMP._IOwnership _1590_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1591_recIdents;
          RAST._IExpr _out194;
          DCOMP._IOwnership _out195;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out196;
          (this).GenExpr(_1588_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out194, out _out195, out _out196);
          _1589_printedExpr = _out194;
          _1590_recOwnership = _out195;
          _1591_recIdents = _out196;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1589_printedExpr)));
          readIdents = _1591_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source76 = range;
      bool unmatched76 = true;
      if (unmatched76) {
        if (_source76.is_NoRange) {
          unmatched76 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched76) {
        if (_source76.is_U8) {
          unmatched76 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched76) {
        if (_source76.is_U16) {
          unmatched76 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched76) {
        if (_source76.is_U32) {
          unmatched76 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched76) {
        if (_source76.is_U64) {
          unmatched76 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched76) {
        if (_source76.is_U128) {
          unmatched76 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched76) {
        if (_source76.is_I8) {
          unmatched76 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched76) {
        if (_source76.is_I16) {
          unmatched76 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched76) {
        if (_source76.is_I32) {
          unmatched76 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched76) {
        if (_source76.is_I64) {
          unmatched76 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched76) {
        if (_source76.is_I128) {
          unmatched76 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched76) {
        DAST._INewtypeRange _1592___v105 = _source76;
        unmatched76 = false;
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
        RAST._IExpr _out197;
        DCOMP._IOwnership _out198;
        (this).FromOwned(r, expectedOwnership, out _out197, out _out198);
        @out = _out197;
        resultingOwnership = _out198;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out199;
        DCOMP._IOwnership _out200;
        (this).FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out199, out _out200);
        @out = _out199;
        resultingOwnership = _out200;
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
      DAST._IExpression _source77 = e;
      bool unmatched77 = true;
      if (unmatched77) {
        if (_source77.is_Literal) {
          DAST._ILiteral _h130 = _source77.dtor_Literal_a0;
          if (_h130.is_BoolLiteral) {
            bool _1593_b = _h130.dtor_BoolLiteral_a0;
            unmatched77 = false;
            {
              RAST._IExpr _out201;
              DCOMP._IOwnership _out202;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1593_b), expectedOwnership, out _out201, out _out202);
              r = _out201;
              resultingOwnership = _out202;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Literal) {
          DAST._ILiteral _h131 = _source77.dtor_Literal_a0;
          if (_h131.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1594_i = _h131.dtor_IntLiteral_a0;
            DAST._IType _1595_t = _h131.dtor_IntLiteral_a1;
            unmatched77 = false;
            {
              DAST._IType _source78 = _1595_t;
              bool unmatched78 = true;
              if (unmatched78) {
                if (_source78.is_Primitive) {
                  DAST._IPrimitive _h70 = _source78.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched78 = false;
                    {
                      if ((new BigInteger((_1594_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1594_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1594_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched78) {
                DAST._IType _1596_o = _source78;
                unmatched78 = false;
                {
                  RAST._IType _1597_genType;
                  RAST._IType _out203;
                  _out203 = (this).GenType(_1596_o, DCOMP.GenTypeContext.@default());
                  _1597_genType = _out203;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1594_i), _1597_genType);
                }
              }
              RAST._IExpr _out204;
              DCOMP._IOwnership _out205;
              (this).FromOwned(r, expectedOwnership, out _out204, out _out205);
              r = _out204;
              resultingOwnership = _out205;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Literal) {
          DAST._ILiteral _h132 = _source77.dtor_Literal_a0;
          if (_h132.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1598_n = _h132.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1599_d = _h132.dtor_DecLiteral_a1;
            DAST._IType _1600_t = _h132.dtor_DecLiteral_a2;
            unmatched77 = false;
            {
              DAST._IType _source79 = _1600_t;
              bool unmatched79 = true;
              if (unmatched79) {
                if (_source79.is_Primitive) {
                  DAST._IPrimitive _h71 = _source79.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched79 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1598_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1599_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched79) {
                DAST._IType _1601_o = _source79;
                unmatched79 = false;
                {
                  RAST._IType _1602_genType;
                  RAST._IType _out206;
                  _out206 = (this).GenType(_1601_o, DCOMP.GenTypeContext.@default());
                  _1602_genType = _out206;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1598_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1599_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1602_genType);
                }
              }
              RAST._IExpr _out207;
              DCOMP._IOwnership _out208;
              (this).FromOwned(r, expectedOwnership, out _out207, out _out208);
              r = _out207;
              resultingOwnership = _out208;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched77) {
        if (_source77.is_Literal) {
          DAST._ILiteral _h133 = _source77.dtor_Literal_a0;
          if (_h133.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1603_l = _h133.dtor_StringLiteral_a0;
            bool _1604_verbatim = _h133.dtor_verbatim;
            unmatched77 = false;
            {
              if (_1604_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1603_l, false, _1604_verbatim));
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
      if (unmatched77) {
        if (_source77.is_Literal) {
          DAST._ILiteral _h134 = _source77.dtor_Literal_a0;
          if (_h134.is_CharLiteralUTF16) {
            BigInteger _1605_c = _h134.dtor_CharLiteralUTF16_a0;
            unmatched77 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1605_c));
              r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
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
      if (unmatched77) {
        if (_source77.is_Literal) {
          DAST._ILiteral _h135 = _source77.dtor_Literal_a0;
          if (_h135.is_CharLiteral) {
            Dafny.Rune _1606_c = _h135.dtor_CharLiteral_a0;
            unmatched77 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1606_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
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
      if (unmatched77) {
        DAST._ILiteral _h136 = _source77.dtor_Literal_a0;
        DAST._IType _1607_tpe = _h136.dtor_Null_a0;
        unmatched77 = false;
        {
          RAST._IType _1608_tpeGen;
          RAST._IType _out215;
          _out215 = (this).GenType(_1607_tpe, DCOMP.GenTypeContext.@default());
          _1608_tpeGen = _out215;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"));
          } else {
            r = RAST.Expr.create_TypeAscription(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1608_tpeGen);
          }
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
    public void GenExprBinary(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IBinOp _1609_op = _let_tmp_rhs53.dtor_op;
      DAST._IExpression _1610_lExpr = _let_tmp_rhs53.dtor_left;
      DAST._IExpression _1611_rExpr = _let_tmp_rhs53.dtor_right;
      DAST.Format._IBinaryOpFormat _1612_format = _let_tmp_rhs53.dtor_format2;
      bool _1613_becomesLeftCallsRight;
      _1613_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source80 = _1609_op;
        bool unmatched80 = true;
        if (unmatched80) {
          bool disjunctiveMatch12 = false;
          if (_source80.is_SetMerge) {
            disjunctiveMatch12 = true;
          }
          if (_source80.is_SetSubtraction) {
            disjunctiveMatch12 = true;
          }
          if (_source80.is_SetIntersection) {
            disjunctiveMatch12 = true;
          }
          if (_source80.is_SetDisjoint) {
            disjunctiveMatch12 = true;
          }
          if (_source80.is_MapMerge) {
            disjunctiveMatch12 = true;
          }
          if (_source80.is_MapSubtraction) {
            disjunctiveMatch12 = true;
          }
          if (_source80.is_MultisetMerge) {
            disjunctiveMatch12 = true;
          }
          if (_source80.is_MultisetSubtraction) {
            disjunctiveMatch12 = true;
          }
          if (_source80.is_MultisetIntersection) {
            disjunctiveMatch12 = true;
          }
          if (_source80.is_MultisetDisjoint) {
            disjunctiveMatch12 = true;
          }
          if (_source80.is_Concat) {
            disjunctiveMatch12 = true;
          }
          if (disjunctiveMatch12) {
            unmatched80 = false;
            return true;
          }
        }
        if (unmatched80) {
          DAST._IBinOp _1614___v106 = _source80;
          unmatched80 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1615_becomesRightCallsLeft;
      _1615_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source81 = _1609_op;
        bool unmatched81 = true;
        if (unmatched81) {
          if (_source81.is_In) {
            unmatched81 = false;
            return true;
          }
        }
        if (unmatched81) {
          DAST._IBinOp _1616___v107 = _source81;
          unmatched81 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1617_becomesCallLeftRight;
      _1617_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source82 = _1609_op;
        bool unmatched82 = true;
        if (unmatched82) {
          if (_source82.is_Eq) {
            bool referential0 = _source82.dtor_referential;
            if ((referential0) == (true)) {
              unmatched82 = false;
              return false;
            }
          }
        }
        if (unmatched82) {
          if (_source82.is_SetMerge) {
            unmatched82 = false;
            return true;
          }
        }
        if (unmatched82) {
          if (_source82.is_SetSubtraction) {
            unmatched82 = false;
            return true;
          }
        }
        if (unmatched82) {
          if (_source82.is_SetIntersection) {
            unmatched82 = false;
            return true;
          }
        }
        if (unmatched82) {
          if (_source82.is_SetDisjoint) {
            unmatched82 = false;
            return true;
          }
        }
        if (unmatched82) {
          if (_source82.is_MapMerge) {
            unmatched82 = false;
            return true;
          }
        }
        if (unmatched82) {
          if (_source82.is_MapSubtraction) {
            unmatched82 = false;
            return true;
          }
        }
        if (unmatched82) {
          if (_source82.is_MultisetMerge) {
            unmatched82 = false;
            return true;
          }
        }
        if (unmatched82) {
          if (_source82.is_MultisetSubtraction) {
            unmatched82 = false;
            return true;
          }
        }
        if (unmatched82) {
          if (_source82.is_MultisetIntersection) {
            unmatched82 = false;
            return true;
          }
        }
        if (unmatched82) {
          if (_source82.is_MultisetDisjoint) {
            unmatched82 = false;
            return true;
          }
        }
        if (unmatched82) {
          if (_source82.is_Concat) {
            unmatched82 = false;
            return true;
          }
        }
        if (unmatched82) {
          DAST._IBinOp _1618___v108 = _source82;
          unmatched82 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1619_expectedLeftOwnership;
      _1619_expectedLeftOwnership = ((_1613_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1615_becomesRightCallsLeft) || (_1617_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1620_expectedRightOwnership;
      _1620_expectedRightOwnership = (((_1613_becomesLeftCallsRight) || (_1617_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1615_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1621_left;
      DCOMP._IOwnership _1622___v109;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1623_recIdentsL;
      RAST._IExpr _out218;
      DCOMP._IOwnership _out219;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out220;
      (this).GenExpr(_1610_lExpr, selfIdent, env, _1619_expectedLeftOwnership, out _out218, out _out219, out _out220);
      _1621_left = _out218;
      _1622___v109 = _out219;
      _1623_recIdentsL = _out220;
      RAST._IExpr _1624_right;
      DCOMP._IOwnership _1625___v110;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1626_recIdentsR;
      RAST._IExpr _out221;
      DCOMP._IOwnership _out222;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out223;
      (this).GenExpr(_1611_rExpr, selfIdent, env, _1620_expectedRightOwnership, out _out221, out _out222, out _out223);
      _1624_right = _out221;
      _1625___v110 = _out222;
      _1626_recIdentsR = _out223;
      DAST._IBinOp _source83 = _1609_op;
      bool unmatched83 = true;
      if (unmatched83) {
        if (_source83.is_In) {
          unmatched83 = false;
          {
            r = ((_1624_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1621_left);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_SeqProperPrefix) {
          unmatched83 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1621_left, _1624_right, _1612_format);
        }
      }
      if (unmatched83) {
        if (_source83.is_SeqPrefix) {
          unmatched83 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1621_left, _1624_right, _1612_format);
        }
      }
      if (unmatched83) {
        if (_source83.is_SetMerge) {
          unmatched83 = false;
          {
            r = ((_1621_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1624_right);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_SetSubtraction) {
          unmatched83 = false;
          {
            r = ((_1621_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1624_right);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_SetIntersection) {
          unmatched83 = false;
          {
            r = ((_1621_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1624_right);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Subset) {
          unmatched83 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1621_left, _1624_right, _1612_format);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_ProperSubset) {
          unmatched83 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1621_left, _1624_right, _1612_format);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_SetDisjoint) {
          unmatched83 = false;
          {
            r = ((_1621_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1624_right);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_MapMerge) {
          unmatched83 = false;
          {
            r = ((_1621_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1624_right);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_MapSubtraction) {
          unmatched83 = false;
          {
            r = ((_1621_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1624_right);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_MultisetMerge) {
          unmatched83 = false;
          {
            r = ((_1621_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1624_right);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_MultisetSubtraction) {
          unmatched83 = false;
          {
            r = ((_1621_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1624_right);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_MultisetIntersection) {
          unmatched83 = false;
          {
            r = ((_1621_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1624_right);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Submultiset) {
          unmatched83 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1621_left, _1624_right, _1612_format);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_ProperSubmultiset) {
          unmatched83 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1621_left, _1624_right, _1612_format);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_MultisetDisjoint) {
          unmatched83 = false;
          {
            r = ((_1621_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1624_right);
          }
        }
      }
      if (unmatched83) {
        if (_source83.is_Concat) {
          unmatched83 = false;
          {
            r = ((_1621_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1624_right);
          }
        }
      }
      if (unmatched83) {
        DAST._IBinOp _1627___v111 = _source83;
        unmatched83 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1609_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1609_op), _1621_left, _1624_right, _1612_format);
          } else {
            DAST._IBinOp _source84 = _1609_op;
            bool unmatched84 = true;
            if (unmatched84) {
              if (_source84.is_Eq) {
                bool _1628_referential = _source84.dtor_referential;
                unmatched84 = false;
                {
                  if (_1628_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1621_left, _1624_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1611_rExpr).is_SeqValue) && ((new BigInteger(((_1611_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1621_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1610_lExpr).is_SeqValue) && ((new BigInteger(((_1610_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1624_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1621_left, _1624_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched84) {
              if (_source84.is_EuclidianDiv) {
                unmatched84 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1621_left, _1624_right));
                }
              }
            }
            if (unmatched84) {
              if (_source84.is_EuclidianMod) {
                unmatched84 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1621_left, _1624_right));
                }
              }
            }
            if (unmatched84) {
              Dafny.ISequence<Dafny.Rune> _1629_op = _source84.dtor_Passthrough_a0;
              unmatched84 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1629_op, _1621_left, _1624_right, _1612_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out224;
      DCOMP._IOwnership _out225;
      (this).FromOwned(r, expectedOwnership, out _out224, out _out225);
      r = _out224;
      resultingOwnership = _out225;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1623_recIdentsL, _1626_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _1630_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _1631_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _1632_toTpe = _let_tmp_rhs54.dtor_typ;
      DAST._IType _let_tmp_rhs55 = _1632_toTpe;
      DAST._IResolvedType _let_tmp_rhs56 = _let_tmp_rhs55.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1633_path = _let_tmp_rhs56.dtor_path;
      Dafny.ISequence<DAST._IType> _1634_typeArgs = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs57 = _let_tmp_rhs56.dtor_kind;
      DAST._IType _1635_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1636_range = _let_tmp_rhs57.dtor_range;
      bool _1637_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1638___v112 = _let_tmp_rhs56.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1639___v113 = _let_tmp_rhs56.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1640___v114 = _let_tmp_rhs56.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1641_nativeToType;
      _1641_nativeToType = DCOMP.COMP.NewtypeToRustType(_1635_b, _1636_range);
      if (object.Equals(_1631_fromTpe, _1635_b)) {
        RAST._IExpr _1642_recursiveGen;
        DCOMP._IOwnership _1643_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1644_recIdents;
        RAST._IExpr _out226;
        DCOMP._IOwnership _out227;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
        (this).GenExpr(_1630_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out226, out _out227, out _out228);
        _1642_recursiveGen = _out226;
        _1643_recOwned = _out227;
        _1644_recIdents = _out228;
        readIdents = _1644_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source85 = _1641_nativeToType;
        bool unmatched85 = true;
        if (unmatched85) {
          if (_source85.is_Some) {
            RAST._IType _1645_v = _source85.dtor_value;
            unmatched85 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1642_recursiveGen, RAST.Expr.create_ExprFromType(_1645_v)));
            RAST._IExpr _out229;
            DCOMP._IOwnership _out230;
            (this).FromOwned(r, expectedOwnership, out _out229, out _out230);
            r = _out229;
            resultingOwnership = _out230;
          }
        }
        if (unmatched85) {
          unmatched85 = false;
          if (_1637_erase) {
            r = _1642_recursiveGen;
          } else {
            RAST._IType _1646_rhsType;
            RAST._IType _out231;
            _out231 = (this).GenType(_1632_toTpe, DCOMP.GenTypeContext.InBinding());
            _1646_rhsType = _out231;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1646_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1642_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out232;
          DCOMP._IOwnership _out233;
          (this).FromOwnership(r, _1643_recOwned, expectedOwnership, out _out232, out _out233);
          r = _out232;
          resultingOwnership = _out233;
        }
      } else {
        if ((_1641_nativeToType).is_Some) {
          DAST._IType _source86 = _1631_fromTpe;
          bool unmatched86 = true;
          if (unmatched86) {
            if (_source86.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source86.dtor_resolved;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1647___v115 = resolved1.dtor_path;
              Dafny.ISequence<DAST._IType> _1648___v116 = resolved1.dtor_typeArgs;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1649_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1650_range0 = kind1.dtor_range;
                bool _1651_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1652_attributes0 = resolved1.dtor_attributes;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1653___v117 = resolved1.dtor_properMethods;
                Dafny.ISequence<DAST._IType> _1654___v118 = resolved1.dtor_extendedTypes;
                unmatched86 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1655_nativeFromType;
                  _1655_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1649_b0, _1650_range0);
                  if ((_1655_nativeFromType).is_Some) {
                    RAST._IExpr _1656_recursiveGen;
                    DCOMP._IOwnership _1657_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1658_recIdents;
                    RAST._IExpr _out234;
                    DCOMP._IOwnership _out235;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out236;
                    (this).GenExpr(_1630_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out234, out _out235, out _out236);
                    _1656_recursiveGen = _out234;
                    _1657_recOwned = _out235;
                    _1658_recIdents = _out236;
                    RAST._IExpr _out237;
                    DCOMP._IOwnership _out238;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1656_recursiveGen, (_1641_nativeToType).dtor_value), _1657_recOwned, expectedOwnership, out _out237, out _out238);
                    r = _out237;
                    resultingOwnership = _out238;
                    readIdents = _1658_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched86) {
            DAST._IType _1659___v119 = _source86;
            unmatched86 = false;
          }
          if (object.Equals(_1631_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1660_recursiveGen;
            DCOMP._IOwnership _1661_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1662_recIdents;
            RAST._IExpr _out239;
            DCOMP._IOwnership _out240;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out241;
            (this).GenExpr(_1630_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out239, out _out240, out _out241);
            _1660_recursiveGen = _out239;
            _1661_recOwned = _out240;
            _1662_recIdents = _out241;
            RAST._IExpr _out242;
            DCOMP._IOwnership _out243;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1660_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1641_nativeToType).dtor_value), _1661_recOwned, expectedOwnership, out _out242, out _out243);
            r = _out242;
            resultingOwnership = _out243;
            readIdents = _1662_recIdents;
            return ;
          }
        }
        RAST._IExpr _out244;
        DCOMP._IOwnership _out245;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out246;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1630_expr, _1631_fromTpe, _1635_b), _1635_b, _1632_toTpe), selfIdent, env, expectedOwnership, out _out244, out _out245, out _out246);
        r = _out244;
        resultingOwnership = _out245;
        readIdents = _out246;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs58 = e;
      DAST._IExpression _1663_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1664_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1665_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _1664_fromTpe;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1666___v120 = _let_tmp_rhs60.dtor_path;
      Dafny.ISequence<DAST._IType> _1667___v121 = _let_tmp_rhs60.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs61 = _let_tmp_rhs60.dtor_kind;
      DAST._IType _1668_b = _let_tmp_rhs61.dtor_baseType;
      DAST._INewtypeRange _1669_range = _let_tmp_rhs61.dtor_range;
      bool _1670_erase = _let_tmp_rhs61.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1671_attributes = _let_tmp_rhs60.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1672___v122 = _let_tmp_rhs60.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1673___v123 = _let_tmp_rhs60.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1674_nativeFromType;
      _1674_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1668_b, _1669_range);
      if (object.Equals(_1668_b, _1665_toTpe)) {
        RAST._IExpr _1675_recursiveGen;
        DCOMP._IOwnership _1676_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1677_recIdents;
        RAST._IExpr _out247;
        DCOMP._IOwnership _out248;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
        (this).GenExpr(_1663_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out247, out _out248, out _out249);
        _1675_recursiveGen = _out247;
        _1676_recOwned = _out248;
        _1677_recIdents = _out249;
        readIdents = _1677_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source87 = _1674_nativeFromType;
        bool unmatched87 = true;
        if (unmatched87) {
          if (_source87.is_Some) {
            RAST._IType _1678_v = _source87.dtor_value;
            unmatched87 = false;
            RAST._IType _1679_toTpeRust;
            RAST._IType _out250;
            _out250 = (this).GenType(_1665_toTpe, DCOMP.GenTypeContext.@default());
            _1679_toTpeRust = _out250;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1679_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1675_recursiveGen));
            RAST._IExpr _out251;
            DCOMP._IOwnership _out252;
            (this).FromOwned(r, expectedOwnership, out _out251, out _out252);
            r = _out251;
            resultingOwnership = _out252;
          }
        }
        if (unmatched87) {
          unmatched87 = false;
          if (_1670_erase) {
            r = _1675_recursiveGen;
          } else {
            r = (_1675_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out253;
          DCOMP._IOwnership _out254;
          (this).FromOwnership(r, _1676_recOwned, expectedOwnership, out _out253, out _out254);
          r = _out253;
          resultingOwnership = _out254;
        }
      } else {
        if ((_1674_nativeFromType).is_Some) {
          if (object.Equals(_1665_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1680_recursiveGen;
            DCOMP._IOwnership _1681_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1682_recIdents;
            RAST._IExpr _out255;
            DCOMP._IOwnership _out256;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out257;
            (this).GenExpr(_1663_expr, selfIdent, env, expectedOwnership, out _out255, out _out256, out _out257);
            _1680_recursiveGen = _out255;
            _1681_recOwned = _out256;
            _1682_recIdents = _out257;
            RAST._IExpr _out258;
            DCOMP._IOwnership _out259;
            (this).FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1680_recursiveGen, (this).DafnyCharUnderlying)), _1681_recOwned, expectedOwnership, out _out258, out _out259);
            r = _out258;
            resultingOwnership = _out259;
            readIdents = _1682_recIdents;
            return ;
          }
        }
        RAST._IExpr _out260;
        DCOMP._IOwnership _out261;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1663_expr, _1664_fromTpe, _1668_b), _1668_b, _1665_toTpe), selfIdent, env, expectedOwnership, out _out260, out _out261, out _out262);
        r = _out260;
        resultingOwnership = _out261;
        readIdents = _out262;
      }
    }
    public void GenExprConvertNotImplemented(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _1683_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _1684_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _1685_toTpe = _let_tmp_rhs62.dtor_typ;
      RAST._IType _1686_fromTpeGen;
      RAST._IType _out263;
      _out263 = (this).GenType(_1684_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1686_fromTpeGen = _out263;
      RAST._IType _1687_toTpeGen;
      RAST._IType _out264;
      _out264 = (this).GenType(_1685_toTpe, DCOMP.GenTypeContext.InBinding());
      _1687_toTpeGen = _out264;
      if (RAST.__default.IsUpcastConversion(_1686_fromTpeGen, _1687_toTpeGen)) {
        RAST._IExpr _1688_recursiveGen;
        DCOMP._IOwnership _1689_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1690_recIdents;
        RAST._IExpr _out265;
        DCOMP._IOwnership _out266;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out267;
        (this).GenExpr(_1683_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out265, out _out266, out _out267);
        _1688_recursiveGen = _out265;
        _1689_recOwned = _out266;
        _1690_recIdents = _out267;
        readIdents = _1690_recIdents;
        if ((_1687_toTpeGen).IsObjectOrPointer()) {
          _1687_toTpeGen = (_1687_toTpeGen).ObjectOrPointerUnderlying();
        }
        r = ((((RAST.__default.dafny__runtime).MSel((this).upcast)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_")), _1687_toTpeGen))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Apply1(_1688_recursiveGen);
        RAST._IExpr _out268;
        DCOMP._IOwnership _out269;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out268, out _out269);
        r = _out268;
        resultingOwnership = _out269;
      } else {
        RAST._IExpr _1691_recursiveGen;
        DCOMP._IOwnership _1692_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1693_recIdents;
        RAST._IExpr _out270;
        DCOMP._IOwnership _out271;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out272;
        (this).GenExpr(_1683_expr, selfIdent, env, expectedOwnership, out _out270, out _out271, out _out272);
        _1691_recursiveGen = _out270;
        _1692_recOwned = _out271;
        _1693_recIdents = _out272;
        readIdents = _1693_recIdents;
        Dafny.ISequence<Dafny.Rune> _1694_msg;
        _1694_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1686_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1687_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1694_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1691_recursiveGen)._ToString(DCOMP.__default.IND), _1694_msg));
        RAST._IExpr _out273;
        DCOMP._IOwnership _out274;
        (this).FromOwnership(r, _1692_recOwned, expectedOwnership, out _out273, out _out274);
        r = _out273;
        resultingOwnership = _out274;
      }
    }
    public void GenExprConvert(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs63 = e;
      DAST._IExpression _1695_expr = _let_tmp_rhs63.dtor_value;
      DAST._IType _1696_fromTpe = _let_tmp_rhs63.dtor_from;
      DAST._IType _1697_toTpe = _let_tmp_rhs63.dtor_typ;
      if (object.Equals(_1696_fromTpe, _1697_toTpe)) {
        RAST._IExpr _1698_recursiveGen;
        DCOMP._IOwnership _1699_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1700_recIdents;
        RAST._IExpr _out275;
        DCOMP._IOwnership _out276;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out277;
        (this).GenExpr(_1695_expr, selfIdent, env, expectedOwnership, out _out275, out _out276, out _out277);
        _1698_recursiveGen = _out275;
        _1699_recOwned = _out276;
        _1700_recIdents = _out277;
        r = _1698_recursiveGen;
        RAST._IExpr _out278;
        DCOMP._IOwnership _out279;
        (this).FromOwnership(r, _1699_recOwned, expectedOwnership, out _out278, out _out279);
        r = _out278;
        resultingOwnership = _out279;
        readIdents = _1700_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source88 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1696_fromTpe, _1697_toTpe);
        bool unmatched88 = true;
        if (unmatched88) {
          DAST._IType _1701___v124 = _source88.dtor__0;
          DAST._IType _12 = _source88.dtor__1;
          if (_12.is_UserDefined) {
            DAST._IResolvedType resolved2 = _12.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1702___v125 = resolved2.dtor_path;
            Dafny.ISequence<DAST._IType> _1703___v126 = resolved2.dtor_typeArgs;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1704_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1705_range = kind2.dtor_range;
              bool _1706_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1707_attributes = resolved2.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1708___v127 = resolved2.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1709___v128 = resolved2.dtor_extendedTypes;
              unmatched88 = false;
              {
                RAST._IExpr _out280;
                DCOMP._IOwnership _out281;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out282;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out280, out _out281, out _out282);
                r = _out280;
                resultingOwnership = _out281;
                readIdents = _out282;
              }
            }
          }
        }
        if (unmatched88) {
          DAST._IType _02 = _source88.dtor__0;
          if (_02.is_UserDefined) {
            DAST._IResolvedType resolved3 = _02.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1710___v129 = resolved3.dtor_path;
            Dafny.ISequence<DAST._IType> _1711___v130 = resolved3.dtor_typeArgs;
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1712_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1713_range = kind3.dtor_range;
              bool _1714_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1715_attributes = resolved3.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1716___v131 = resolved3.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1717___v132 = resolved3.dtor_extendedTypes;
              DAST._IType _1718___v133 = _source88.dtor__1;
              unmatched88 = false;
              {
                RAST._IExpr _out283;
                DCOMP._IOwnership _out284;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out285;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out283, out _out284, out _out285);
                r = _out283;
                resultingOwnership = _out284;
                readIdents = _out285;
              }
            }
          }
        }
        if (unmatched88) {
          DAST._IType _03 = _source88.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h72 = _03.dtor_Primitive_a0;
            if (_h72.is_Int) {
              DAST._IType _13 = _source88.dtor__1;
              if (_13.is_Primitive) {
                DAST._IPrimitive _h73 = _13.dtor_Primitive_a0;
                if (_h73.is_Real) {
                  unmatched88 = false;
                  {
                    RAST._IExpr _1719_recursiveGen;
                    DCOMP._IOwnership _1720___v134;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1721_recIdents;
                    RAST._IExpr _out286;
                    DCOMP._IOwnership _out287;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out288;
                    (this).GenExpr(_1695_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out286, out _out287, out _out288);
                    _1719_recursiveGen = _out286;
                    _1720___v134 = _out287;
                    _1721_recIdents = _out288;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1719_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out289;
                    DCOMP._IOwnership _out290;
                    (this).FromOwned(r, expectedOwnership, out _out289, out _out290);
                    r = _out289;
                    resultingOwnership = _out290;
                    readIdents = _1721_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched88) {
          DAST._IType _04 = _source88.dtor__0;
          if (_04.is_Primitive) {
            DAST._IPrimitive _h74 = _04.dtor_Primitive_a0;
            if (_h74.is_Real) {
              DAST._IType _14 = _source88.dtor__1;
              if (_14.is_Primitive) {
                DAST._IPrimitive _h75 = _14.dtor_Primitive_a0;
                if (_h75.is_Int) {
                  unmatched88 = false;
                  {
                    RAST._IExpr _1722_recursiveGen;
                    DCOMP._IOwnership _1723___v135;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1724_recIdents;
                    RAST._IExpr _out291;
                    DCOMP._IOwnership _out292;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out293;
                    (this).GenExpr(_1695_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out291, out _out292, out _out293);
                    _1722_recursiveGen = _out291;
                    _1723___v135 = _out292;
                    _1724_recIdents = _out293;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1722_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out294;
                    DCOMP._IOwnership _out295;
                    (this).FromOwned(r, expectedOwnership, out _out294, out _out295);
                    r = _out294;
                    resultingOwnership = _out295;
                    readIdents = _1724_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched88) {
          DAST._IType _05 = _source88.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h76 = _05.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _15 = _source88.dtor__1;
              if (_15.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1725___v136 = _15.dtor_Passthrough_a0;
                unmatched88 = false;
                {
                  RAST._IType _1726_rhsType;
                  RAST._IType _out296;
                  _out296 = (this).GenType(_1697_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1726_rhsType = _out296;
                  RAST._IExpr _1727_recursiveGen;
                  DCOMP._IOwnership _1728___v137;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1729_recIdents;
                  RAST._IExpr _out297;
                  DCOMP._IOwnership _out298;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out299;
                  (this).GenExpr(_1695_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out297, out _out298, out _out299);
                  _1727_recursiveGen = _out297;
                  _1728___v137 = _out298;
                  _1729_recIdents = _out299;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1726_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1727_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out300;
                  DCOMP._IOwnership _out301;
                  (this).FromOwned(r, expectedOwnership, out _out300, out _out301);
                  r = _out300;
                  resultingOwnership = _out301;
                  readIdents = _1729_recIdents;
                }
              }
            }
          }
        }
        if (unmatched88) {
          DAST._IType _06 = _source88.dtor__0;
          if (_06.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1730___v138 = _06.dtor_Passthrough_a0;
            DAST._IType _16 = _source88.dtor__1;
            if (_16.is_Primitive) {
              DAST._IPrimitive _h77 = _16.dtor_Primitive_a0;
              if (_h77.is_Int) {
                unmatched88 = false;
                {
                  RAST._IType _1731_rhsType;
                  RAST._IType _out302;
                  _out302 = (this).GenType(_1696_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1731_rhsType = _out302;
                  RAST._IExpr _1732_recursiveGen;
                  DCOMP._IOwnership _1733___v139;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1734_recIdents;
                  RAST._IExpr _out303;
                  DCOMP._IOwnership _out304;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out305;
                  (this).GenExpr(_1695_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out303, out _out304, out _out305);
                  _1732_recursiveGen = _out303;
                  _1733___v139 = _out304;
                  _1734_recIdents = _out305;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1732_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out306;
                  DCOMP._IOwnership _out307;
                  (this).FromOwned(r, expectedOwnership, out _out306, out _out307);
                  r = _out306;
                  resultingOwnership = _out307;
                  readIdents = _1734_recIdents;
                }
              }
            }
          }
        }
        if (unmatched88) {
          DAST._IType _07 = _source88.dtor__0;
          if (_07.is_Primitive) {
            DAST._IPrimitive _h78 = _07.dtor_Primitive_a0;
            if (_h78.is_Int) {
              DAST._IType _17 = _source88.dtor__1;
              if (_17.is_Primitive) {
                DAST._IPrimitive _h79 = _17.dtor_Primitive_a0;
                if (_h79.is_Char) {
                  unmatched88 = false;
                  {
                    RAST._IType _1735_rhsType;
                    RAST._IType _out308;
                    _out308 = (this).GenType(_1697_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1735_rhsType = _out308;
                    RAST._IExpr _1736_recursiveGen;
                    DCOMP._IOwnership _1737___v140;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1738_recIdents;
                    RAST._IExpr _out309;
                    DCOMP._IOwnership _out310;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out311;
                    (this).GenExpr(_1695_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out309, out _out310, out _out311);
                    _1736_recursiveGen = _out309;
                    _1737___v140 = _out310;
                    _1738_recIdents = _out311;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1736_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out312;
                    DCOMP._IOwnership _out313;
                    (this).FromOwned(r, expectedOwnership, out _out312, out _out313);
                    r = _out312;
                    resultingOwnership = _out313;
                    readIdents = _1738_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched88) {
          DAST._IType _08 = _source88.dtor__0;
          if (_08.is_Primitive) {
            DAST._IPrimitive _h710 = _08.dtor_Primitive_a0;
            if (_h710.is_Char) {
              DAST._IType _18 = _source88.dtor__1;
              if (_18.is_Primitive) {
                DAST._IPrimitive _h711 = _18.dtor_Primitive_a0;
                if (_h711.is_Int) {
                  unmatched88 = false;
                  {
                    RAST._IType _1739_rhsType;
                    RAST._IType _out314;
                    _out314 = (this).GenType(_1696_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1739_rhsType = _out314;
                    RAST._IExpr _1740_recursiveGen;
                    DCOMP._IOwnership _1741___v141;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1742_recIdents;
                    RAST._IExpr _out315;
                    DCOMP._IOwnership _out316;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out317;
                    (this).GenExpr(_1695_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out315, out _out316, out _out317);
                    _1740_recursiveGen = _out315;
                    _1741___v141 = _out316;
                    _1742_recIdents = _out317;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1740_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out318;
                    DCOMP._IOwnership _out319;
                    (this).FromOwned(r, expectedOwnership, out _out318, out _out319);
                    r = _out318;
                    resultingOwnership = _out319;
                    readIdents = _1742_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched88) {
          DAST._IType _09 = _source88.dtor__0;
          if (_09.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1743___v142 = _09.dtor_Passthrough_a0;
            DAST._IType _19 = _source88.dtor__1;
            if (_19.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1744___v143 = _19.dtor_Passthrough_a0;
              unmatched88 = false;
              {
                RAST._IExpr _1745_recursiveGen;
                DCOMP._IOwnership _1746___v144;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1747_recIdents;
                RAST._IExpr _out320;
                DCOMP._IOwnership _out321;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out322;
                (this).GenExpr(_1695_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out320, out _out321, out _out322);
                _1745_recursiveGen = _out320;
                _1746___v144 = _out321;
                _1747_recIdents = _out322;
                RAST._IType _1748_toTpeGen;
                RAST._IType _out323;
                _out323 = (this).GenType(_1697_toTpe, DCOMP.GenTypeContext.InBinding());
                _1748_toTpeGen = _out323;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1745_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1748_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out324;
                DCOMP._IOwnership _out325;
                (this).FromOwned(r, expectedOwnership, out _out324, out _out325);
                r = _out324;
                resultingOwnership = _out325;
                readIdents = _1747_recIdents;
              }
            }
          }
        }
        if (unmatched88) {
          _System._ITuple2<DAST._IType, DAST._IType> _1749___v145 = _source88;
          unmatched88 = false;
          {
            RAST._IExpr _out326;
            DCOMP._IOwnership _out327;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out328;
            (this).GenExprConvertNotImplemented(e, selfIdent, env, expectedOwnership, out _out326, out _out327, out _out328);
            r = _out326;
            resultingOwnership = _out327;
            readIdents = _out328;
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
      Std.Wrappers._IOption<RAST._IType> _1750_tpe;
      _1750_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1751_placeboOpt;
      _1751_placeboOpt = (((_1750_tpe).is_Some) ? (((_1750_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1752_currentlyBorrowed;
      _1752_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1753_noNeedOfClone;
      _1753_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1751_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1752_currentlyBorrowed = false;
        _1753_noNeedOfClone = true;
        _1750_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1751_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_1752_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1750_tpe).is_Some) && (((_1750_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1754_needObjectFromRef;
        _1754_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source89 = (selfIdent).dtor_dafnyType;
          bool unmatched89 = true;
          if (unmatched89) {
            if (_source89.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source89.dtor_resolved;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1755___v146 = resolved4.dtor_path;
              Dafny.ISequence<DAST._IType> _1756___v147 = resolved4.dtor_typeArgs;
              DAST._IResolvedTypeBase _1757_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1758_attributes = resolved4.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1759___v148 = resolved4.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1760___v149 = resolved4.dtor_extendedTypes;
              unmatched89 = false;
              return ((_1757_base).is_Class) || ((_1757_base).is_Trait);
            }
          }
          if (unmatched89) {
            DAST._IType _1761___v150 = _source89;
            unmatched89 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_1754_needObjectFromRef) {
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1753_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1753_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1752_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1750_tpe).is_Some) && (((_1750_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1762_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1762_attributes).UniqueElements, false, (((_exists_var_1) => {
        DAST._IAttribute _1763_attribute = (DAST._IAttribute)_exists_var_1;
        return ((_1762_attributes).Contains(_1763_attribute)) && ((((_1763_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1763_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      BigInteger _hi36 = new BigInteger((args).Count);
      for (BigInteger _1764_i = BigInteger.Zero; _1764_i < _hi36; _1764_i++) {
        DCOMP._IOwnership _1765_argOwnership;
        _1765_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if (((name).is_CallName) && ((_1764_i) < (new BigInteger((((name).dtor_signature)).Count)))) {
          RAST._IType _1766_tpe;
          RAST._IType _out329;
          _out329 = (this).GenType(((((name).dtor_signature)).Select(_1764_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1766_tpe = _out329;
          if ((_1766_tpe).CanReadWithoutClone()) {
            _1765_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1767_argExpr;
        DCOMP._IOwnership _1768___v151;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1769_argIdents;
        RAST._IExpr _out330;
        DCOMP._IOwnership _out331;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out332;
        (this).GenExpr((args).Select(_1764_i), selfIdent, env, _1765_argOwnership, out _out330, out _out331, out _out332);
        _1767_argExpr = _out330;
        _1768___v151 = _out331;
        _1769_argIdents = _out332;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1767_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1769_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi37 = new BigInteger((typeArgs).Count);
      for (BigInteger _1770_typeI = BigInteger.Zero; _1770_typeI < _hi37; _1770_typeI++) {
        RAST._IType _1771_typeExpr;
        RAST._IType _out333;
        _out333 = (this).GenType((typeArgs).Select(_1770_typeI), DCOMP.GenTypeContext.@default());
        _1771_typeExpr = _out333;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1771_typeExpr));
      }
      fullNameQualifier = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
        DAST._ICallName _source90 = name;
        bool unmatched90 = true;
        if (unmatched90) {
          if (_source90.is_CallName) {
            Dafny.ISequence<Dafny.Rune> _1772_nameIdent = _source90.dtor_name;
            Std.Wrappers._IOption<DAST._IType> onType1 = _source90.dtor_onType;
            if (onType1.is_Some) {
              DAST._IType value10 = onType1.dtor_value;
              if (value10.is_UserDefined) {
                DAST._IResolvedType _1773_resolvedType = value10.dtor_resolved;
                Std.Wrappers._IOption<DAST._IFormal> _1774___v152 = _source90.dtor_receiverArgs;
                Dafny.ISequence<DAST._IFormal> _1775___v153 = _source90.dtor_signature;
                unmatched90 = false;
                if ((((_1773_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_1776_resolvedType, _1777_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(((_1776_resolvedType).dtor_properMethods).UniqueElements, true, (((_forall_var_8) => {
                  Dafny.ISequence<Dafny.Rune> _1778_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                  return !(((_1776_resolvedType).dtor_properMethods).Contains(_1778_m)) || (!object.Equals((_1778_m), _1777_nameIdent));
                }))))(_1773_resolvedType, _1772_nameIdent))) {
                  return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_1773_resolvedType, (_1772_nameIdent)), _1773_resolvedType));
                } else {
                  return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
                }
              }
            }
          }
        }
        if (unmatched90) {
          DAST._ICallName _1779___v154 = _source90;
          unmatched90 = false;
          return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
        }
        throw new System.Exception("unexpected control point");
      }))();
      if ((((((fullNameQualifier).is_Some) && ((selfIdent).is_ThisTyped)) && (((selfIdent).dtor_dafnyType).is_UserDefined)) && ((this).IsSameResolvedType(((selfIdent).dtor_dafnyType).dtor_resolved, (fullNameQualifier).dtor_value))) && (!((this).HasExternAttributeRenamingModule(((fullNameQualifier).dtor_value).dtor_attributes)))) {
        fullNameQualifier = Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      }
    }
    public void GenExpr(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _source91 = e;
      bool unmatched91 = true;
      if (unmatched91) {
        if (_source91.is_Literal) {
          DAST._ILiteral _1780___v155 = _source91.dtor_Literal_a0;
          unmatched91 = false;
          RAST._IExpr _out334;
          DCOMP._IOwnership _out335;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out336;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out334, out _out335, out _out336);
          r = _out334;
          resultingOwnership = _out335;
          readIdents = _out336;
        }
      }
      if (unmatched91) {
        if (_source91.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1781_name = _source91.dtor_Ident_a0;
          unmatched91 = false;
          {
            RAST._IExpr _out337;
            DCOMP._IOwnership _out338;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out339;
            (this).GenIdent(DCOMP.__default.escapeName(_1781_name), selfIdent, env, expectedOwnership, out _out337, out _out338, out _out339);
            r = _out337;
            resultingOwnership = _out338;
            readIdents = _out339;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1782_path = _source91.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _1783_typeArgs = _source91.dtor_typeArgs;
          unmatched91 = false;
          {
            RAST._IExpr _out340;
            _out340 = DCOMP.COMP.GenPathExpr(_1782_path);
            r = _out340;
            if ((new BigInteger((_1783_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1784_typeExprs;
              _1784_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi38 = new BigInteger((_1783_typeArgs).Count);
              for (BigInteger _1785_i = BigInteger.Zero; _1785_i < _hi38; _1785_i++) {
                RAST._IType _1786_typeExpr;
                RAST._IType _out341;
                _out341 = (this).GenType((_1783_typeArgs).Select(_1785_i), DCOMP.GenTypeContext.@default());
                _1786_typeExpr = _out341;
                _1784_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1784_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1786_typeExpr));
              }
              r = (r).ApplyType(_1784_typeExprs);
            }
            if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowed())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
            } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
              resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
            } else {
              RAST._IExpr _out342;
              DCOMP._IOwnership _out343;
              (this).FromOwned(r, expectedOwnership, out _out342, out _out343);
              r = _out342;
              resultingOwnership = _out343;
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_InitializationValue) {
          DAST._IType _1787_typ = _source91.dtor_typ;
          unmatched91 = false;
          {
            RAST._IType _1788_typExpr;
            RAST._IType _out344;
            _out344 = (this).GenType(_1787_typ, DCOMP.GenTypeContext.@default());
            _1788_typExpr = _out344;
            if ((_1788_typExpr).IsObjectOrPointer()) {
              r = (_1788_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1788_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            }
            RAST._IExpr _out345;
            DCOMP._IOwnership _out346;
            (this).FromOwned(r, expectedOwnership, out _out345, out _out346);
            r = _out345;
            resultingOwnership = _out346;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1789_values = _source91.dtor_Tuple_a0;
          unmatched91 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1790_exprs;
            _1790_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi39 = new BigInteger((_1789_values).Count);
            for (BigInteger _1791_i = BigInteger.Zero; _1791_i < _hi39; _1791_i++) {
              RAST._IExpr _1792_recursiveGen;
              DCOMP._IOwnership _1793___v156;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1794_recIdents;
              RAST._IExpr _out347;
              DCOMP._IOwnership _out348;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
              (this).GenExpr((_1789_values).Select(_1791_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out347, out _out348, out _out349);
              _1792_recursiveGen = _out347;
              _1793___v156 = _out348;
              _1794_recIdents = _out349;
              _1790_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1790_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1792_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1794_recIdents);
            }
            r = (((new BigInteger((_1789_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1790_exprs)) : (RAST.__default.SystemTuple(_1790_exprs)));
            RAST._IExpr _out350;
            DCOMP._IOwnership _out351;
            (this).FromOwned(r, expectedOwnership, out _out350, out _out351);
            r = _out350;
            resultingOwnership = _out351;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1795_path = _source91.dtor_path;
          Dafny.ISequence<DAST._IType> _1796_typeArgs = _source91.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1797_args = _source91.dtor_args;
          unmatched91 = false;
          {
            RAST._IExpr _out352;
            _out352 = DCOMP.COMP.GenPathExpr(_1795_path);
            r = _out352;
            if ((new BigInteger((_1796_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1798_typeExprs;
              _1798_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_1796_typeArgs).Count);
              for (BigInteger _1799_i = BigInteger.Zero; _1799_i < _hi40; _1799_i++) {
                RAST._IType _1800_typeExpr;
                RAST._IType _out353;
                _out353 = (this).GenType((_1796_typeArgs).Select(_1799_i), DCOMP.GenTypeContext.@default());
                _1800_typeExpr = _out353;
                _1798_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1798_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1800_typeExpr));
              }
              r = (r).ApplyType(_1798_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1801_arguments;
            _1801_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi41 = new BigInteger((_1797_args).Count);
            for (BigInteger _1802_i = BigInteger.Zero; _1802_i < _hi41; _1802_i++) {
              RAST._IExpr _1803_recursiveGen;
              DCOMP._IOwnership _1804___v157;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1805_recIdents;
              RAST._IExpr _out354;
              DCOMP._IOwnership _out355;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out356;
              (this).GenExpr((_1797_args).Select(_1802_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out354, out _out355, out _out356);
              _1803_recursiveGen = _out354;
              _1804___v157 = _out355;
              _1805_recIdents = _out356;
              _1801_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1801_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1803_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1805_recIdents);
            }
            r = (r).Apply(_1801_arguments);
            RAST._IExpr _out357;
            DCOMP._IOwnership _out358;
            (this).FromOwned(r, expectedOwnership, out _out357, out _out358);
            r = _out357;
            resultingOwnership = _out358;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _1806_dims = _source91.dtor_dims;
          DAST._IType _1807_typ = _source91.dtor_typ;
          unmatched91 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1806_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1808_msg;
              _1808_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1808_msg);
              }
              r = RAST.Expr.create_RawExpr(_1808_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1809_typeGen;
              RAST._IType _out359;
              _out359 = (this).GenType(_1807_typ, DCOMP.GenTypeContext.@default());
              _1809_typeGen = _out359;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1810_dimExprs;
              _1810_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi42 = new BigInteger((_1806_dims).Count);
              for (BigInteger _1811_i = BigInteger.Zero; _1811_i < _hi42; _1811_i++) {
                RAST._IExpr _1812_recursiveGen;
                DCOMP._IOwnership _1813___v158;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1814_recIdents;
                RAST._IExpr _out360;
                DCOMP._IOwnership _out361;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out362;
                (this).GenExpr((_1806_dims).Select(_1811_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out360, out _out361, out _out362);
                _1812_recursiveGen = _out360;
                _1813___v158 = _out361;
                _1814_recIdents = _out362;
                _1810_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1810_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_TypeAscription(_1812_recursiveGen, RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("usize")))));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1814_recIdents);
              }
              if ((new BigInteger((_1806_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1815_class__name;
                _1815_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1806_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1815_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1809_typeGen))).MSel((this).placebos__usize)).Apply(_1810_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1809_typeGen))).Apply(_1810_dimExprs);
              }
            }
            RAST._IExpr _out363;
            DCOMP._IOwnership _out364;
            (this).FromOwned(r, expectedOwnership, out _out363, out _out364);
            r = _out363;
            resultingOwnership = _out364;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_ArrayIndexToInt) {
          DAST._IExpression _1816_underlying = _source91.dtor_value;
          unmatched91 = false;
          {
            RAST._IExpr _1817_recursiveGen;
            DCOMP._IOwnership _1818___v159;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1819_recIdents;
            RAST._IExpr _out365;
            DCOMP._IOwnership _out366;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out367;
            (this).GenExpr(_1816_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out365, out _out366, out _out367);
            _1817_recursiveGen = _out365;
            _1818___v159 = _out366;
            _1819_recIdents = _out367;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1817_recursiveGen);
            readIdents = _1819_recIdents;
            RAST._IExpr _out368;
            DCOMP._IOwnership _out369;
            (this).FromOwned(r, expectedOwnership, out _out368, out _out369);
            r = _out368;
            resultingOwnership = _out369;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_FinalizeNewArray) {
          DAST._IExpression _1820_underlying = _source91.dtor_value;
          DAST._IType _1821_typ = _source91.dtor_typ;
          unmatched91 = false;
          {
            RAST._IType _1822_tpe;
            RAST._IType _out370;
            _out370 = (this).GenType(_1821_typ, DCOMP.GenTypeContext.@default());
            _1822_tpe = _out370;
            RAST._IExpr _1823_recursiveGen;
            DCOMP._IOwnership _1824___v160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1825_recIdents;
            RAST._IExpr _out371;
            DCOMP._IOwnership _out372;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out373;
            (this).GenExpr(_1820_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out371, out _out372, out _out373);
            _1823_recursiveGen = _out371;
            _1824___v160 = _out372;
            _1825_recIdents = _out373;
            readIdents = _1825_recIdents;
            if ((_1822_tpe).IsObjectOrPointer()) {
              RAST._IType _1826_t;
              _1826_t = (_1822_tpe).ObjectOrPointerUnderlying();
              if ((_1826_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1823_recursiveGen);
              } else if ((_1826_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1827_c;
                _1827_c = (_1826_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1827_c)).MSel((this).array__construct)).Apply1(_1823_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1822_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1822_tpe)._ToString(DCOMP.__default.IND)));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            }
            RAST._IExpr _out374;
            DCOMP._IOwnership _out375;
            (this).FromOwned(r, expectedOwnership, out _out374, out _out375);
            r = _out374;
            resultingOwnership = _out375;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_DatatypeValue) {
          DAST._IResolvedType _1828_datatypeType = _source91.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1829_typeArgs = _source91.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1830_variant = _source91.dtor_variant;
          bool _1831_isCo = _source91.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1832_values = _source91.dtor_contents;
          unmatched91 = false;
          {
            RAST._IExpr _out376;
            _out376 = DCOMP.COMP.GenPathExpr((_1828_datatypeType).dtor_path);
            r = _out376;
            Dafny.ISequence<RAST._IType> _1833_genTypeArgs;
            _1833_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi43 = new BigInteger((_1829_typeArgs).Count);
            for (BigInteger _1834_i = BigInteger.Zero; _1834_i < _hi43; _1834_i++) {
              RAST._IType _1835_typeExpr;
              RAST._IType _out377;
              _out377 = (this).GenType((_1829_typeArgs).Select(_1834_i), DCOMP.GenTypeContext.@default());
              _1835_typeExpr = _out377;
              _1833_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1833_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1835_typeExpr));
            }
            if ((new BigInteger((_1829_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1833_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1830_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1836_assignments;
            _1836_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi44 = new BigInteger((_1832_values).Count);
            for (BigInteger _1837_i = BigInteger.Zero; _1837_i < _hi44; _1837_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs64 = (_1832_values).Select(_1837_i);
              Dafny.ISequence<Dafny.Rune> _1838_name = _let_tmp_rhs64.dtor__0;
              DAST._IExpression _1839_value = _let_tmp_rhs64.dtor__1;
              if (_1831_isCo) {
                RAST._IExpr _1840_recursiveGen;
                DCOMP._IOwnership _1841___v161;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1842_recIdents;
                RAST._IExpr _out378;
                DCOMP._IOwnership _out379;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out380;
                (this).GenExpr(_1839_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out378, out _out379, out _out380);
                _1840_recursiveGen = _out378;
                _1841___v161 = _out379;
                _1842_recIdents = _out380;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1842_recIdents);
                Dafny.ISequence<Dafny.Rune> _1843_allReadCloned;
                _1843_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1842_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1844_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1842_recIdents).Elements) {
                    _1844_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1842_recIdents).Contains(_1844_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4068)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1843_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1843_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1844_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1844_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1842_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1842_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1844_next));
                }
                Dafny.ISequence<Dafny.Rune> _1845_wasAssigned;
                _1845_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1843_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1840_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1836_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1836_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1838_name), RAST.Expr.create_RawExpr(_1845_wasAssigned))));
              } else {
                RAST._IExpr _1846_recursiveGen;
                DCOMP._IOwnership _1847___v162;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1848_recIdents;
                RAST._IExpr _out381;
                DCOMP._IOwnership _out382;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
                (this).GenExpr(_1839_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out381, out _out382, out _out383);
                _1846_recursiveGen = _out381;
                _1847___v162 = _out382;
                _1848_recIdents = _out383;
                _1836_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1836_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1838_name), _1846_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1848_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1836_assignments);
            if ((this).IsRcWrapped((_1828_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out384;
            DCOMP._IOwnership _out385;
            (this).FromOwned(r, expectedOwnership, out _out384, out _out385);
            r = _out384;
            resultingOwnership = _out385;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_Convert) {
          DAST._IExpression _1849___v163 = _source91.dtor_value;
          DAST._IType _1850___v164 = _source91.dtor_from;
          DAST._IType _1851___v165 = _source91.dtor_typ;
          unmatched91 = false;
          {
            RAST._IExpr _out386;
            DCOMP._IOwnership _out387;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out388;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out386, out _out387, out _out388);
            r = _out386;
            resultingOwnership = _out387;
            readIdents = _out388;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_SeqConstruct) {
          DAST._IExpression _1852_length = _source91.dtor_length;
          DAST._IExpression _1853_expr = _source91.dtor_elem;
          unmatched91 = false;
          {
            RAST._IExpr _1854_recursiveGen;
            DCOMP._IOwnership _1855___v166;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1856_recIdents;
            RAST._IExpr _out389;
            DCOMP._IOwnership _out390;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
            (this).GenExpr(_1853_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out389, out _out390, out _out391);
            _1854_recursiveGen = _out389;
            _1855___v166 = _out390;
            _1856_recIdents = _out391;
            RAST._IExpr _1857_lengthGen;
            DCOMP._IOwnership _1858___v167;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1859_lengthIdents;
            RAST._IExpr _out392;
            DCOMP._IOwnership _out393;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out394;
            (this).GenExpr(_1852_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out392, out _out393, out _out394);
            _1857_lengthGen = _out392;
            _1858___v167 = _out393;
            _1859_lengthIdents = _out394;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1854_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1857_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1856_recIdents, _1859_lengthIdents);
            RAST._IExpr _out395;
            DCOMP._IOwnership _out396;
            (this).FromOwned(r, expectedOwnership, out _out395, out _out396);
            r = _out395;
            resultingOwnership = _out396;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1860_exprs = _source91.dtor_elements;
          DAST._IType _1861_typ = _source91.dtor_typ;
          unmatched91 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1862_genTpe;
            RAST._IType _out397;
            _out397 = (this).GenType(_1861_typ, DCOMP.GenTypeContext.@default());
            _1862_genTpe = _out397;
            BigInteger _1863_i;
            _1863_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1864_args;
            _1864_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1863_i) < (new BigInteger((_1860_exprs).Count))) {
              RAST._IExpr _1865_recursiveGen;
              DCOMP._IOwnership _1866___v168;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1867_recIdents;
              RAST._IExpr _out398;
              DCOMP._IOwnership _out399;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
              (this).GenExpr((_1860_exprs).Select(_1863_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out398, out _out399, out _out400);
              _1865_recursiveGen = _out398;
              _1866___v168 = _out399;
              _1867_recIdents = _out400;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1867_recIdents);
              _1864_args = Dafny.Sequence<RAST._IExpr>.Concat(_1864_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1865_recursiveGen));
              _1863_i = (_1863_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1864_args);
            if ((new BigInteger((_1864_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1862_genTpe));
            }
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            (this).FromOwned(r, expectedOwnership, out _out401, out _out402);
            r = _out401;
            resultingOwnership = _out402;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1868_exprs = _source91.dtor_elements;
          unmatched91 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1869_generatedValues;
            _1869_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1870_i;
            _1870_i = BigInteger.Zero;
            while ((_1870_i) < (new BigInteger((_1868_exprs).Count))) {
              RAST._IExpr _1871_recursiveGen;
              DCOMP._IOwnership _1872___v169;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1873_recIdents;
              RAST._IExpr _out403;
              DCOMP._IOwnership _out404;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out405;
              (this).GenExpr((_1868_exprs).Select(_1870_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out403, out _out404, out _out405);
              _1871_recursiveGen = _out403;
              _1872___v169 = _out404;
              _1873_recIdents = _out405;
              _1869_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1869_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1871_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1873_recIdents);
              _1870_i = (_1870_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1869_generatedValues);
            RAST._IExpr _out406;
            DCOMP._IOwnership _out407;
            (this).FromOwned(r, expectedOwnership, out _out406, out _out407);
            r = _out406;
            resultingOwnership = _out407;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1874_exprs = _source91.dtor_elements;
          unmatched91 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1875_generatedValues;
            _1875_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1876_i;
            _1876_i = BigInteger.Zero;
            while ((_1876_i) < (new BigInteger((_1874_exprs).Count))) {
              RAST._IExpr _1877_recursiveGen;
              DCOMP._IOwnership _1878___v170;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1879_recIdents;
              RAST._IExpr _out408;
              DCOMP._IOwnership _out409;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out410;
              (this).GenExpr((_1874_exprs).Select(_1876_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out408, out _out409, out _out410);
              _1877_recursiveGen = _out408;
              _1878___v170 = _out409;
              _1879_recIdents = _out410;
              _1875_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1875_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1877_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1879_recIdents);
              _1876_i = (_1876_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1875_generatedValues);
            RAST._IExpr _out411;
            DCOMP._IOwnership _out412;
            (this).FromOwned(r, expectedOwnership, out _out411, out _out412);
            r = _out411;
            resultingOwnership = _out412;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_ToMultiset) {
          DAST._IExpression _1880_expr = _source91.dtor_ToMultiset_a0;
          unmatched91 = false;
          {
            RAST._IExpr _1881_recursiveGen;
            DCOMP._IOwnership _1882___v171;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1883_recIdents;
            RAST._IExpr _out413;
            DCOMP._IOwnership _out414;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
            (this).GenExpr(_1880_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out413, out _out414, out _out415);
            _1881_recursiveGen = _out413;
            _1882___v171 = _out414;
            _1883_recIdents = _out415;
            r = ((_1881_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1883_recIdents;
            RAST._IExpr _out416;
            DCOMP._IOwnership _out417;
            (this).FromOwned(r, expectedOwnership, out _out416, out _out417);
            r = _out416;
            resultingOwnership = _out417;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1884_mapElems = _source91.dtor_mapElems;
          unmatched91 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1885_generatedValues;
            _1885_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1886_i;
            _1886_i = BigInteger.Zero;
            while ((_1886_i) < (new BigInteger((_1884_mapElems).Count))) {
              RAST._IExpr _1887_recursiveGenKey;
              DCOMP._IOwnership _1888___v172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1889_recIdentsKey;
              RAST._IExpr _out418;
              DCOMP._IOwnership _out419;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out420;
              (this).GenExpr(((_1884_mapElems).Select(_1886_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out418, out _out419, out _out420);
              _1887_recursiveGenKey = _out418;
              _1888___v172 = _out419;
              _1889_recIdentsKey = _out420;
              RAST._IExpr _1890_recursiveGenValue;
              DCOMP._IOwnership _1891___v173;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1892_recIdentsValue;
              RAST._IExpr _out421;
              DCOMP._IOwnership _out422;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out423;
              (this).GenExpr(((_1884_mapElems).Select(_1886_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out421, out _out422, out _out423);
              _1890_recursiveGenValue = _out421;
              _1891___v173 = _out422;
              _1892_recIdentsValue = _out423;
              _1885_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1885_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1887_recursiveGenKey, _1890_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1889_recIdentsKey), _1892_recIdentsValue);
              _1886_i = (_1886_i) + (BigInteger.One);
            }
            _1886_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1893_arguments;
            _1893_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1886_i) < (new BigInteger((_1885_generatedValues).Count))) {
              RAST._IExpr _1894_genKey;
              _1894_genKey = ((_1885_generatedValues).Select(_1886_i)).dtor__0;
              RAST._IExpr _1895_genValue;
              _1895_genValue = ((_1885_generatedValues).Select(_1886_i)).dtor__1;
              _1893_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1893_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1894_genKey, _1895_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1886_i = (_1886_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1893_arguments);
            RAST._IExpr _out424;
            DCOMP._IOwnership _out425;
            (this).FromOwned(r, expectedOwnership, out _out424, out _out425);
            r = _out424;
            resultingOwnership = _out425;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_SeqUpdate) {
          DAST._IExpression _1896_expr = _source91.dtor_expr;
          DAST._IExpression _1897_index = _source91.dtor_indexExpr;
          DAST._IExpression _1898_value = _source91.dtor_value;
          unmatched91 = false;
          {
            RAST._IExpr _1899_exprR;
            DCOMP._IOwnership _1900___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1901_exprIdents;
            RAST._IExpr _out426;
            DCOMP._IOwnership _out427;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out428;
            (this).GenExpr(_1896_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out426, out _out427, out _out428);
            _1899_exprR = _out426;
            _1900___v174 = _out427;
            _1901_exprIdents = _out428;
            RAST._IExpr _1902_indexR;
            DCOMP._IOwnership _1903_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1904_indexIdents;
            RAST._IExpr _out429;
            DCOMP._IOwnership _out430;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out431;
            (this).GenExpr(_1897_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out429, out _out430, out _out431);
            _1902_indexR = _out429;
            _1903_indexOwnership = _out430;
            _1904_indexIdents = _out431;
            RAST._IExpr _1905_valueR;
            DCOMP._IOwnership _1906_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1907_valueIdents;
            RAST._IExpr _out432;
            DCOMP._IOwnership _out433;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out434;
            (this).GenExpr(_1898_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out432, out _out433, out _out434);
            _1905_valueR = _out432;
            _1906_valueOwnership = _out433;
            _1907_valueIdents = _out434;
            r = ((_1899_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1902_indexR, _1905_valueR));
            RAST._IExpr _out435;
            DCOMP._IOwnership _out436;
            (this).FromOwned(r, expectedOwnership, out _out435, out _out436);
            r = _out435;
            resultingOwnership = _out436;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1901_exprIdents, _1904_indexIdents), _1907_valueIdents);
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_MapUpdate) {
          DAST._IExpression _1908_expr = _source91.dtor_expr;
          DAST._IExpression _1909_index = _source91.dtor_indexExpr;
          DAST._IExpression _1910_value = _source91.dtor_value;
          unmatched91 = false;
          {
            RAST._IExpr _1911_exprR;
            DCOMP._IOwnership _1912___v175;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1913_exprIdents;
            RAST._IExpr _out437;
            DCOMP._IOwnership _out438;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
            (this).GenExpr(_1908_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out437, out _out438, out _out439);
            _1911_exprR = _out437;
            _1912___v175 = _out438;
            _1913_exprIdents = _out439;
            RAST._IExpr _1914_indexR;
            DCOMP._IOwnership _1915_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1916_indexIdents;
            RAST._IExpr _out440;
            DCOMP._IOwnership _out441;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out442;
            (this).GenExpr(_1909_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out440, out _out441, out _out442);
            _1914_indexR = _out440;
            _1915_indexOwnership = _out441;
            _1916_indexIdents = _out442;
            RAST._IExpr _1917_valueR;
            DCOMP._IOwnership _1918_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1919_valueIdents;
            RAST._IExpr _out443;
            DCOMP._IOwnership _out444;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out445;
            (this).GenExpr(_1910_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out443, out _out444, out _out445);
            _1917_valueR = _out443;
            _1918_valueOwnership = _out444;
            _1919_valueIdents = _out445;
            r = ((_1911_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1914_indexR, _1917_valueR));
            RAST._IExpr _out446;
            DCOMP._IOwnership _out447;
            (this).FromOwned(r, expectedOwnership, out _out446, out _out447);
            r = _out446;
            resultingOwnership = _out447;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1913_exprIdents, _1916_indexIdents), _1919_valueIdents);
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_This) {
          unmatched91 = false;
          {
            DCOMP._ISelfInfo _source92 = selfIdent;
            bool unmatched92 = true;
            if (unmatched92) {
              if (_source92.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _1920_id = _source92.dtor_rSelfName;
                DAST._IType _1921_dafnyType = _source92.dtor_dafnyType;
                unmatched92 = false;
                {
                  RAST._IExpr _out448;
                  DCOMP._IOwnership _out449;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out450;
                  (this).GenIdent(_1920_id, selfIdent, env, expectedOwnership, out _out448, out _out449, out _out450);
                  r = _out448;
                  resultingOwnership = _out449;
                  readIdents = _out450;
                }
              }
            }
            if (unmatched92) {
              DCOMP._ISelfInfo _1922_None = _source92;
              unmatched92 = false;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out451;
                DCOMP._IOwnership _out452;
                (this).FromOwned(r, expectedOwnership, out _out451, out _out452);
                r = _out451;
                resultingOwnership = _out452;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_Ite) {
          DAST._IExpression _1923_cond = _source91.dtor_cond;
          DAST._IExpression _1924_t = _source91.dtor_thn;
          DAST._IExpression _1925_f = _source91.dtor_els;
          unmatched91 = false;
          {
            RAST._IExpr _1926_cond;
            DCOMP._IOwnership _1927___v176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1928_recIdentsCond;
            RAST._IExpr _out453;
            DCOMP._IOwnership _out454;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out455;
            (this).GenExpr(_1923_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out453, out _out454, out _out455);
            _1926_cond = _out453;
            _1927___v176 = _out454;
            _1928_recIdentsCond = _out455;
            RAST._IExpr _1929_fExpr;
            DCOMP._IOwnership _1930_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1931_recIdentsF;
            RAST._IExpr _out456;
            DCOMP._IOwnership _out457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out458;
            (this).GenExpr(_1925_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out456, out _out457, out _out458);
            _1929_fExpr = _out456;
            _1930_fOwned = _out457;
            _1931_recIdentsF = _out458;
            RAST._IExpr _1932_tExpr;
            DCOMP._IOwnership _1933___v177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1934_recIdentsT;
            RAST._IExpr _out459;
            DCOMP._IOwnership _out460;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out461;
            (this).GenExpr(_1924_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out459, out _out460, out _out461);
            _1932_tExpr = _out459;
            _1933___v177 = _out460;
            _1934_recIdentsT = _out461;
            r = RAST.Expr.create_IfExpr(_1926_cond, _1932_tExpr, _1929_fExpr);
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out462, out _out463);
            r = _out462;
            resultingOwnership = _out463;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1928_recIdentsCond, _1934_recIdentsT), _1931_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source91.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1935_e = _source91.dtor_expr;
            DAST.Format._IUnaryOpFormat _1936_format = _source91.dtor_format1;
            unmatched91 = false;
            {
              RAST._IExpr _1937_recursiveGen;
              DCOMP._IOwnership _1938___v178;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1939_recIdents;
              RAST._IExpr _out464;
              DCOMP._IOwnership _out465;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
              (this).GenExpr(_1935_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out464, out _out465, out _out466);
              _1937_recursiveGen = _out464;
              _1938___v178 = _out465;
              _1939_recIdents = _out466;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1937_recursiveGen, _1936_format);
              RAST._IExpr _out467;
              DCOMP._IOwnership _out468;
              (this).FromOwned(r, expectedOwnership, out _out467, out _out468);
              r = _out467;
              resultingOwnership = _out468;
              readIdents = _1939_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source91.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1940_e = _source91.dtor_expr;
            DAST.Format._IUnaryOpFormat _1941_format = _source91.dtor_format1;
            unmatched91 = false;
            {
              RAST._IExpr _1942_recursiveGen;
              DCOMP._IOwnership _1943___v179;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1944_recIdents;
              RAST._IExpr _out469;
              DCOMP._IOwnership _out470;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out471;
              (this).GenExpr(_1940_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out469, out _out470, out _out471);
              _1942_recursiveGen = _out469;
              _1943___v179 = _out470;
              _1944_recIdents = _out471;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1942_recursiveGen, _1941_format);
              RAST._IExpr _out472;
              DCOMP._IOwnership _out473;
              (this).FromOwned(r, expectedOwnership, out _out472, out _out473);
              r = _out472;
              resultingOwnership = _out473;
              readIdents = _1944_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source91.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _1945_e = _source91.dtor_expr;
            DAST.Format._IUnaryOpFormat _1946_format = _source91.dtor_format1;
            unmatched91 = false;
            {
              RAST._IExpr _1947_recursiveGen;
              DCOMP._IOwnership _1948_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1949_recIdents;
              RAST._IExpr _out474;
              DCOMP._IOwnership _out475;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out476;
              (this).GenExpr(_1945_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out474, out _out475, out _out476);
              _1947_recursiveGen = _out474;
              _1948_recOwned = _out475;
              _1949_recIdents = _out476;
              r = ((_1947_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out477;
              DCOMP._IOwnership _out478;
              (this).FromOwned(r, expectedOwnership, out _out477, out _out478);
              r = _out477;
              resultingOwnership = _out478;
              readIdents = _1949_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_BinOp) {
          DAST._IBinOp _1950___v180 = _source91.dtor_op;
          DAST._IExpression _1951___v181 = _source91.dtor_left;
          DAST._IExpression _1952___v182 = _source91.dtor_right;
          DAST.Format._IBinaryOpFormat _1953___v183 = _source91.dtor_format2;
          unmatched91 = false;
          RAST._IExpr _out479;
          DCOMP._IOwnership _out480;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out481;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out479, out _out480, out _out481);
          r = _out479;
          resultingOwnership = _out480;
          readIdents = _out481;
        }
      }
      if (unmatched91) {
        if (_source91.is_ArrayLen) {
          DAST._IExpression _1954_expr = _source91.dtor_expr;
          DAST._IType _1955_exprType = _source91.dtor_exprType;
          BigInteger _1956_dim = _source91.dtor_dim;
          bool _1957_native = _source91.dtor_native;
          unmatched91 = false;
          {
            RAST._IExpr _1958_recursiveGen;
            DCOMP._IOwnership _1959___v184;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1960_recIdents;
            RAST._IExpr _out482;
            DCOMP._IOwnership _out483;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
            (this).GenExpr(_1954_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out482, out _out483, out _out484);
            _1958_recursiveGen = _out482;
            _1959___v184 = _out483;
            _1960_recIdents = _out484;
            RAST._IType _1961_arrayType;
            RAST._IType _out485;
            _out485 = (this).GenType(_1955_exprType, DCOMP.GenTypeContext.@default());
            _1961_arrayType = _out485;
            if (!((_1961_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _1962_msg;
              _1962_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_1961_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1962_msg);
              r = RAST.Expr.create_RawExpr(_1962_msg);
            } else {
              RAST._IType _1963_underlying;
              _1963_underlying = (_1961_arrayType).ObjectOrPointerUnderlying();
              if (((_1956_dim).Sign == 0) && ((_1963_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_1958_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_1956_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_1958_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = (((this).read__macro).Apply1(_1958_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Length"), Std.Strings.__default.OfNat(_1956_dim)));
                }
              }
              if (!(_1957_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out486;
            DCOMP._IOwnership _out487;
            (this).FromOwned(r, expectedOwnership, out _out486, out _out487);
            r = _out486;
            resultingOwnership = _out487;
            readIdents = _1960_recIdents;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_MapKeys) {
          DAST._IExpression _1964_expr = _source91.dtor_expr;
          unmatched91 = false;
          {
            RAST._IExpr _1965_recursiveGen;
            DCOMP._IOwnership _1966___v185;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1967_recIdents;
            RAST._IExpr _out488;
            DCOMP._IOwnership _out489;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
            (this).GenExpr(_1964_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out488, out _out489, out _out490);
            _1965_recursiveGen = _out488;
            _1966___v185 = _out489;
            _1967_recIdents = _out490;
            readIdents = _1967_recIdents;
            r = ((_1965_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out491;
            DCOMP._IOwnership _out492;
            (this).FromOwned(r, expectedOwnership, out _out491, out _out492);
            r = _out491;
            resultingOwnership = _out492;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_MapValues) {
          DAST._IExpression _1968_expr = _source91.dtor_expr;
          unmatched91 = false;
          {
            RAST._IExpr _1969_recursiveGen;
            DCOMP._IOwnership _1970___v186;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1971_recIdents;
            RAST._IExpr _out493;
            DCOMP._IOwnership _out494;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out495;
            (this).GenExpr(_1968_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out493, out _out494, out _out495);
            _1969_recursiveGen = _out493;
            _1970___v186 = _out494;
            _1971_recIdents = _out495;
            readIdents = _1971_recIdents;
            r = ((_1969_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out496;
            DCOMP._IOwnership _out497;
            (this).FromOwned(r, expectedOwnership, out _out496, out _out497);
            r = _out496;
            resultingOwnership = _out497;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_SelectFn) {
          DAST._IExpression _1972_on = _source91.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1973_field = _source91.dtor_field;
          bool _1974_isDatatype = _source91.dtor_onDatatype;
          bool _1975_isStatic = _source91.dtor_isStatic;
          BigInteger _1976_arity = _source91.dtor_arity;
          unmatched91 = false;
          {
            RAST._IExpr _1977_onExpr;
            DCOMP._IOwnership _1978_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1979_recIdents;
            RAST._IExpr _out498;
            DCOMP._IOwnership _out499;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
            (this).GenExpr(_1972_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out498, out _out499, out _out500);
            _1977_onExpr = _out498;
            _1978_onOwned = _out499;
            _1979_recIdents = _out500;
            Dafny.ISequence<Dafny.Rune> _1980_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _1981_onString;
            _1981_onString = (_1977_onExpr)._ToString(DCOMP.__default.IND);
            if (_1975_isStatic) {
              _1980_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1981_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_1973_field));
            } else {
              _1980_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _1980_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1980_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _1981_onString), ((object.Equals(_1978_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _1982_args;
              _1982_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _1983_i;
              _1983_i = BigInteger.Zero;
              while ((_1983_i) < (_1976_arity)) {
                if ((_1983_i).Sign == 1) {
                  _1982_args = Dafny.Sequence<Dafny.Rune>.Concat(_1982_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _1982_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1982_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_1983_i));
                _1983_i = (_1983_i) + (BigInteger.One);
              }
              _1980_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1980_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _1982_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _1980_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1980_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_1973_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1982_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _1980_s = Dafny.Sequence<Dafny.Rune>.Concat(_1980_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _1980_s = Dafny.Sequence<Dafny.Rune>.Concat(_1980_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _1984_typeShape;
            _1984_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _1985_i;
            _1985_i = BigInteger.Zero;
            while ((_1985_i) < (_1976_arity)) {
              if ((_1985_i).Sign == 1) {
                _1984_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1984_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1984_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1984_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _1985_i = (_1985_i) + (BigInteger.One);
            }
            _1984_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1984_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _1980_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _1980_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _1984_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_1980_s);
            RAST._IExpr _out501;
            DCOMP._IOwnership _out502;
            (this).FromOwned(r, expectedOwnership, out _out501, out _out502);
            r = _out501;
            resultingOwnership = _out502;
            readIdents = _1979_recIdents;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_Select) {
          DAST._IExpression expr0 = _source91.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1986_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<DAST._IType> _1987_typeArgs = expr0.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _1988_field = _source91.dtor_field;
            bool _1989_isConstant = _source91.dtor_isConstant;
            bool _1990_isDatatype = _source91.dtor_onDatatype;
            DAST._IType _1991_fieldType = _source91.dtor_fieldType;
            unmatched91 = false;
            {
              RAST._IExpr _1992_onExpr;
              DCOMP._IOwnership _1993_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1994_recIdents;
              RAST._IExpr _out503;
              DCOMP._IOwnership _out504;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
              (this).GenExpr(DAST.Expression.create_Companion(_1986_c, _1987_typeArgs), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out503, out _out504, out _out505);
              _1992_onExpr = _out503;
              _1993_onOwned = _out504;
              _1994_recIdents = _out505;
              r = ((_1992_onExpr).MSel(DCOMP.__default.escapeName(_1988_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out506;
              DCOMP._IOwnership _out507;
              (this).FromOwned(r, expectedOwnership, out _out506, out _out507);
              r = _out506;
              resultingOwnership = _out507;
              readIdents = _1994_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_Select) {
          DAST._IExpression _1995_on = _source91.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1996_field = _source91.dtor_field;
          bool _1997_isConstant = _source91.dtor_isConstant;
          bool _1998_isDatatype = _source91.dtor_onDatatype;
          DAST._IType _1999_fieldType = _source91.dtor_fieldType;
          unmatched91 = false;
          {
            if (_1998_isDatatype) {
              RAST._IExpr _2000_onExpr;
              DCOMP._IOwnership _2001_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2002_recIdents;
              RAST._IExpr _out508;
              DCOMP._IOwnership _out509;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out510;
              (this).GenExpr(_1995_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out508, out _out509, out _out510);
              _2000_onExpr = _out508;
              _2001_onOwned = _out509;
              _2002_recIdents = _out510;
              r = ((_2000_onExpr).Sel(DCOMP.__default.escapeName(_1996_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2003_typ;
              RAST._IType _out511;
              _out511 = (this).GenType(_1999_fieldType, DCOMP.GenTypeContext.@default());
              _2003_typ = _out511;
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out512, out _out513);
              r = _out512;
              resultingOwnership = _out513;
              readIdents = _2002_recIdents;
            } else {
              RAST._IExpr _2004_onExpr;
              DCOMP._IOwnership _2005_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2006_recIdents;
              RAST._IExpr _out514;
              DCOMP._IOwnership _out515;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out516;
              (this).GenExpr(_1995_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out514, out _out515, out _out516);
              _2004_onExpr = _out514;
              _2005_onOwned = _out515;
              _2006_recIdents = _out516;
              r = _2004_onExpr;
              if (!object.Equals(_2004_onExpr, RAST.__default.self)) {
                RAST._IExpr _source93 = _2004_onExpr;
                bool unmatched93 = true;
                if (unmatched93) {
                  if (_source93.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source93.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source93.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name21 = underlying5.dtor_name;
                        if (object.Equals(name21, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          DAST.Format._IUnaryOpFormat _2007___v187 = _source93.dtor_format;
                          unmatched93 = false;
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                        }
                      }
                    }
                  }
                }
                if (unmatched93) {
                  RAST._IExpr _2008___v188 = _source93;
                  unmatched93 = false;
                }
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeName(_1996_field));
              if (_1997_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out517;
              DCOMP._IOwnership _out518;
              (this).FromOwned(r, expectedOwnership, out _out517, out _out518);
              r = _out517;
              resultingOwnership = _out518;
              readIdents = _2006_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_Index) {
          DAST._IExpression _2009_on = _source91.dtor_expr;
          DAST._ICollKind _2010_collKind = _source91.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2011_indices = _source91.dtor_indices;
          unmatched91 = false;
          {
            RAST._IExpr _2012_onExpr;
            DCOMP._IOwnership _2013_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2014_recIdents;
            RAST._IExpr _out519;
            DCOMP._IOwnership _out520;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
            (this).GenExpr(_2009_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out519, out _out520, out _out521);
            _2012_onExpr = _out519;
            _2013_onOwned = _out520;
            _2014_recIdents = _out521;
            readIdents = _2014_recIdents;
            r = _2012_onExpr;
            BigInteger _2015_i;
            _2015_i = BigInteger.Zero;
            while ((_2015_i) < (new BigInteger((_2011_indices).Count))) {
              if (object.Equals(_2010_collKind, DAST.CollKind.create_Array())) {
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              RAST._IExpr _2016_idx;
              DCOMP._IOwnership _2017_idxOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2018_recIdentsIdx;
              RAST._IExpr _out522;
              DCOMP._IOwnership _out523;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out524;
              (this).GenExpr((_2011_indices).Select(_2015_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out522, out _out523, out _out524);
              _2016_idx = _out522;
              _2017_idxOwned = _out523;
              _2018_recIdentsIdx = _out524;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2016_idx);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2018_recIdentsIdx);
              _2015_i = (_2015_i) + (BigInteger.One);
            }
            RAST._IExpr _out525;
            DCOMP._IOwnership _out526;
            (this).FromOwned(r, expectedOwnership, out _out525, out _out526);
            r = _out525;
            resultingOwnership = _out526;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_IndexRange) {
          DAST._IExpression _2019_on = _source91.dtor_expr;
          bool _2020_isArray = _source91.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2021_low = _source91.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2022_high = _source91.dtor_high;
          unmatched91 = false;
          {
            RAST._IExpr _2023_onExpr;
            DCOMP._IOwnership _2024_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2025_recIdents;
            RAST._IExpr _out527;
            DCOMP._IOwnership _out528;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
            (this).GenExpr(_2019_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out527, out _out528, out _out529);
            _2023_onExpr = _out527;
            _2024_onOwned = _out528;
            _2025_recIdents = _out529;
            readIdents = _2025_recIdents;
            Dafny.ISequence<Dafny.Rune> _2026_methodName;
            _2026_methodName = (((_2021_low).is_Some) ? ((((_2022_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2022_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2027_arguments;
            _2027_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source94 = _2021_low;
            bool unmatched94 = true;
            if (unmatched94) {
              if (_source94.is_Some) {
                DAST._IExpression _2028_l = _source94.dtor_value;
                unmatched94 = false;
                {
                  RAST._IExpr _2029_lExpr;
                  DCOMP._IOwnership _2030___v189;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2031_recIdentsL;
                  RAST._IExpr _out530;
                  DCOMP._IOwnership _out531;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out532;
                  (this).GenExpr(_2028_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out530, out _out531, out _out532);
                  _2029_lExpr = _out530;
                  _2030___v189 = _out531;
                  _2031_recIdentsL = _out532;
                  _2027_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2027_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2029_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2031_recIdentsL);
                }
              }
            }
            if (unmatched94) {
              unmatched94 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source95 = _2022_high;
            bool unmatched95 = true;
            if (unmatched95) {
              if (_source95.is_Some) {
                DAST._IExpression _2032_h = _source95.dtor_value;
                unmatched95 = false;
                {
                  RAST._IExpr _2033_hExpr;
                  DCOMP._IOwnership _2034___v190;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2035_recIdentsH;
                  RAST._IExpr _out533;
                  DCOMP._IOwnership _out534;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
                  (this).GenExpr(_2032_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out533, out _out534, out _out535);
                  _2033_hExpr = _out533;
                  _2034___v190 = _out534;
                  _2035_recIdentsH = _out535;
                  _2027_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2027_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2033_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2035_recIdentsH);
                }
              }
            }
            if (unmatched95) {
              unmatched95 = false;
            }
            r = _2023_onExpr;
            if (_2020_isArray) {
              if (!(_2026_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2026_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2026_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2026_methodName))).Apply(_2027_arguments);
            } else {
              if (!(_2026_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2026_methodName)).Apply(_2027_arguments);
              }
            }
            RAST._IExpr _out536;
            DCOMP._IOwnership _out537;
            (this).FromOwned(r, expectedOwnership, out _out536, out _out537);
            r = _out536;
            resultingOwnership = _out537;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_TupleSelect) {
          DAST._IExpression _2036_on = _source91.dtor_expr;
          BigInteger _2037_idx = _source91.dtor_index;
          DAST._IType _2038_fieldType = _source91.dtor_fieldType;
          unmatched91 = false;
          {
            RAST._IExpr _2039_onExpr;
            DCOMP._IOwnership _2040_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2041_recIdents;
            RAST._IExpr _out538;
            DCOMP._IOwnership _out539;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out540;
            (this).GenExpr(_2036_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out538, out _out539, out _out540);
            _2039_onExpr = _out538;
            _2040_onOwnership = _out539;
            _2041_recIdents = _out540;
            Dafny.ISequence<Dafny.Rune> _2042_selName;
            _2042_selName = Std.Strings.__default.OfNat(_2037_idx);
            DAST._IType _source96 = _2038_fieldType;
            bool unmatched96 = true;
            if (unmatched96) {
              if (_source96.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2043_tps = _source96.dtor_Tuple_a0;
                unmatched96 = false;
                if (((_2038_fieldType).is_Tuple) && ((new BigInteger((_2043_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2042_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2042_selName);
                }
              }
            }
            if (unmatched96) {
              DAST._IType _2044___v191 = _source96;
              unmatched96 = false;
            }
            r = (_2039_onExpr).Sel(_2042_selName);
            RAST._IExpr _out541;
            DCOMP._IOwnership _out542;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out541, out _out542);
            r = _out541;
            resultingOwnership = _out542;
            readIdents = _2041_recIdents;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_Call) {
          DAST._IExpression _2045_on = _source91.dtor_on;
          DAST._ICallName _2046_name = _source91.dtor_callName;
          Dafny.ISequence<DAST._IType> _2047_typeArgs = _source91.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2048_args = _source91.dtor_args;
          unmatched91 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2049_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2050_recIdents;
            Dafny.ISequence<RAST._IType> _2051_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2052_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out543;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
            Dafny.ISequence<RAST._IType> _out545;
            Std.Wrappers._IOption<DAST._IResolvedType> _out546;
            (this).GenArgs(selfIdent, _2046_name, _2047_typeArgs, _2048_args, env, out _out543, out _out544, out _out545, out _out546);
            _2049_argExprs = _out543;
            _2050_recIdents = _out544;
            _2051_typeExprs = _out545;
            _2052_fullNameQualifier = _out546;
            readIdents = _2050_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source97 = _2052_fullNameQualifier;
            bool unmatched97 = true;
            if (unmatched97) {
              if (_source97.is_Some) {
                DAST._IResolvedType value11 = _source97.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2053_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2054_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2055_base = value11.dtor_kind;
                Dafny.ISequence<DAST._IAttribute> _2056___v192 = value11.dtor_attributes;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2057___v193 = value11.dtor_properMethods;
                Dafny.ISequence<DAST._IType> _2058___v194 = value11.dtor_extendedTypes;
                unmatched97 = false;
                RAST._IExpr _2059_fullPath;
                RAST._IExpr _out547;
                _out547 = DCOMP.COMP.GenPathExpr(_2053_path);
                _2059_fullPath = _out547;
                Dafny.ISequence<RAST._IType> _2060_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out548;
                _out548 = (this).GenTypeArgs(_2054_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2060_onTypeExprs = _out548;
                RAST._IExpr _2061_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2062_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2063_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2055_base).is_Trait) || ((_2055_base).is_Class)) {
                  RAST._IExpr _out549;
                  DCOMP._IOwnership _out550;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out551;
                  (this).GenExpr(_2045_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out549, out _out550, out _out551);
                  _2061_onExpr = _out549;
                  _2062_recOwnership = _out550;
                  _2063_recIdents = _out551;
                  _2061_onExpr = ((this).read__macro).Apply1(_2061_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2063_recIdents);
                } else {
                  RAST._IExpr _out552;
                  DCOMP._IOwnership _out553;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out554;
                  (this).GenExpr(_2045_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out552, out _out553, out _out554);
                  _2061_onExpr = _out552;
                  _2062_recOwnership = _out553;
                  _2063_recIdents = _out554;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2063_recIdents);
                }
                r = ((((_2059_fullPath).ApplyType(_2060_onTypeExprs)).MSel(DCOMP.__default.escapeName((_2046_name).dtor_name))).ApplyType(_2051_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2061_onExpr), _2049_argExprs));
                RAST._IExpr _out555;
                DCOMP._IOwnership _out556;
                (this).FromOwned(r, expectedOwnership, out _out555, out _out556);
                r = _out555;
                resultingOwnership = _out556;
              }
            }
            if (unmatched97) {
              Std.Wrappers._IOption<DAST._IResolvedType> _2064___v195 = _source97;
              unmatched97 = false;
              RAST._IExpr _2065_onExpr;
              DCOMP._IOwnership _2066___v196;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2067_recIdents;
              RAST._IExpr _out557;
              DCOMP._IOwnership _out558;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out559;
              (this).GenExpr(_2045_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out557, out _out558, out _out559);
              _2065_onExpr = _out557;
              _2066___v196 = _out558;
              _2067_recIdents = _out559;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2067_recIdents);
              Dafny.ISequence<Dafny.Rune> _2068_renderedName;
              _2068_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
                DAST._ICallName _source98 = _2046_name;
                bool unmatched98 = true;
                if (unmatched98) {
                  if (_source98.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _2069_ident = _source98.dtor_name;
                    Std.Wrappers._IOption<DAST._IType> _2070___v197 = _source98.dtor_onType;
                    Std.Wrappers._IOption<DAST._IFormal> _2071___v198 = _source98.dtor_receiverArgs;
                    Dafny.ISequence<DAST._IFormal> _2072___v199 = _source98.dtor_signature;
                    unmatched98 = false;
                    return DCOMP.__default.escapeName(_2069_ident);
                  }
                }
                if (unmatched98) {
                  bool disjunctiveMatch13 = false;
                  if (_source98.is_MapBuilderAdd) {
                    disjunctiveMatch13 = true;
                  }
                  if (_source98.is_SetBuilderAdd) {
                    disjunctiveMatch13 = true;
                  }
                  if (disjunctiveMatch13) {
                    unmatched98 = false;
                    return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  }
                }
                if (unmatched98) {
                  bool disjunctiveMatch14 = false;
                  disjunctiveMatch14 = true;
                  disjunctiveMatch14 = true;
                  if (disjunctiveMatch14) {
                    unmatched98 = false;
                    return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                  }
                }
                throw new System.Exception("unexpected control point");
              }))();
              DAST._IExpression _source99 = _2045_on;
              bool unmatched99 = true;
              if (unmatched99) {
                if (_source99.is_Companion) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2073___v200 = _source99.dtor_Companion_a0;
                  Dafny.ISequence<DAST._IType> _2074___v201 = _source99.dtor_typeArgs;
                  unmatched99 = false;
                  {
                    _2065_onExpr = (_2065_onExpr).MSel(_2068_renderedName);
                  }
                }
              }
              if (unmatched99) {
                DAST._IExpression _2075___v202 = _source99;
                unmatched99 = false;
                {
                  if (!object.Equals(_2065_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source100 = _2046_name;
                    bool unmatched100 = true;
                    if (unmatched100) {
                      if (_source100.is_CallName) {
                        Dafny.ISequence<Dafny.Rune> _2076___v203 = _source100.dtor_name;
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source100.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2077_tpe = onType2.dtor_value;
                          Std.Wrappers._IOption<DAST._IFormal> _2078___v204 = _source100.dtor_receiverArgs;
                          Dafny.ISequence<DAST._IFormal> _2079___v205 = _source100.dtor_signature;
                          unmatched100 = false;
                          RAST._IType _2080_typ;
                          RAST._IType _out560;
                          _out560 = (this).GenType(_2077_tpe, DCOMP.GenTypeContext.@default());
                          _2080_typ = _out560;
                          if ((_2080_typ).IsObjectOrPointer()) {
                            _2065_onExpr = ((this).read__macro).Apply1(_2065_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched100) {
                      DAST._ICallName _2081___v206 = _source100;
                      unmatched100 = false;
                    }
                  }
                  _2065_onExpr = (_2065_onExpr).Sel(_2068_renderedName);
                }
              }
              r = ((_2065_onExpr).ApplyType(_2051_typeExprs)).Apply(_2049_argExprs);
              RAST._IExpr _out561;
              DCOMP._IOwnership _out562;
              (this).FromOwned(r, expectedOwnership, out _out561, out _out562);
              r = _out561;
              resultingOwnership = _out562;
              return ;
            }
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2082_paramsDafny = _source91.dtor_params;
          DAST._IType _2083_retType = _source91.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2084_body = _source91.dtor_body;
          unmatched91 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2085_params;
            Dafny.ISequence<RAST._IFormal> _out563;
            _out563 = (this).GenParams(_2082_paramsDafny);
            _2085_params = _out563;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2086_paramNames;
            _2086_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2087_paramTypesMap;
            _2087_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi45 = new BigInteger((_2085_params).Count);
            for (BigInteger _2088_i = BigInteger.Zero; _2088_i < _hi45; _2088_i++) {
              Dafny.ISequence<Dafny.Rune> _2089_name;
              _2089_name = ((_2085_params).Select(_2088_i)).dtor_name;
              _2086_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2086_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2089_name));
              _2087_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2087_paramTypesMap, _2089_name, ((_2085_params).Select(_2088_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2090_subEnv;
            _2090_subEnv = (env).merge(DCOMP.Environment.create(_2086_paramNames, _2087_paramTypesMap));
            RAST._IExpr _2091_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2092_recIdents;
            DCOMP._IEnvironment _2093___v207;
            RAST._IExpr _out564;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
            DCOMP._IEnvironment _out566;
            (this).GenStmts(_2084_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2090_subEnv, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out564, out _out565, out _out566);
            _2091_recursiveGen = _out564;
            _2092_recIdents = _out565;
            _2093___v207 = _out566;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2092_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2092_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2094_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_2094_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2095_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
                if ((_2094_paramNames).Contains(_2095_name)) {
                  _coll6.Add(_2095_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
            }))())(_2086_paramNames));
            RAST._IExpr _2096_allReadCloned;
            _2096_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2092_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2097_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2092_recIdents).Elements) {
                _2097_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_2092_recIdents).Contains(_2097_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 4530)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2097_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2098_selfCloned;
                DCOMP._IOwnership _2099___v208;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2100___v209;
                RAST._IExpr _out567;
                DCOMP._IOwnership _out568;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out569;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out567, out _out568, out _out569);
                _2098_selfCloned = _out567;
                _2099___v208 = _out568;
                _2100___v209 = _out569;
                _2096_allReadCloned = (_2096_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2098_selfCloned)));
              } else if (!((_2086_paramNames).Contains(_2097_next))) {
                RAST._IExpr _2101_copy;
                _2101_copy = (RAST.Expr.create_Identifier(_2097_next)).Clone();
                _2096_allReadCloned = (_2096_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2097_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2101_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2097_next));
              }
              _2092_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2092_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2097_next));
            }
            RAST._IType _2102_retTypeGen;
            RAST._IType _out570;
            _out570 = (this).GenType(_2083_retType, DCOMP.GenTypeContext.InFn());
            _2102_retTypeGen = _out570;
            r = RAST.Expr.create_Block((_2096_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2085_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2102_retTypeGen), RAST.Expr.create_Block(_2091_recursiveGen)))));
            RAST._IExpr _out571;
            DCOMP._IOwnership _out572;
            (this).FromOwned(r, expectedOwnership, out _out571, out _out572);
            r = _out571;
            resultingOwnership = _out572;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2103_values = _source91.dtor_values;
          DAST._IType _2104_retType = _source91.dtor_retType;
          DAST._IExpression _2105_expr = _source91.dtor_expr;
          unmatched91 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2106_paramNames;
            _2106_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2107_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out573;
            _out573 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2108_value) => {
              return (_2108_value).dtor__0;
            })), _2103_values));
            _2107_paramFormals = _out573;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2109_paramTypes;
            _2109_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2110_paramNamesSet;
            _2110_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi46 = new BigInteger((_2103_values).Count);
            for (BigInteger _2111_i = BigInteger.Zero; _2111_i < _hi46; _2111_i++) {
              Dafny.ISequence<Dafny.Rune> _2112_name;
              _2112_name = (((_2103_values).Select(_2111_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2113_rName;
              _2113_rName = DCOMP.__default.escapeName(_2112_name);
              _2106_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2106_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2113_rName));
              _2109_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2109_paramTypes, _2113_rName, ((_2107_paramFormals).Select(_2111_i)).dtor_tpe);
              _2110_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2110_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2113_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi47 = new BigInteger((_2103_values).Count);
            for (BigInteger _2114_i = BigInteger.Zero; _2114_i < _hi47; _2114_i++) {
              RAST._IType _2115_typeGen;
              RAST._IType _out574;
              _out574 = (this).GenType((((_2103_values).Select(_2114_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2115_typeGen = _out574;
              RAST._IExpr _2116_valueGen;
              DCOMP._IOwnership _2117___v210;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2118_recIdents;
              RAST._IExpr _out575;
              DCOMP._IOwnership _out576;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out577;
              (this).GenExpr(((_2103_values).Select(_2114_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out575, out _out576, out _out577);
              _2116_valueGen = _out575;
              _2117___v210 = _out576;
              _2118_recIdents = _out577;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_2103_values).Select(_2114_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2115_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2116_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2118_recIdents);
            }
            DCOMP._IEnvironment _2119_newEnv;
            _2119_newEnv = DCOMP.Environment.create(_2106_paramNames, _2109_paramTypes);
            RAST._IExpr _2120_recGen;
            DCOMP._IOwnership _2121_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2122_recIdents;
            RAST._IExpr _out578;
            DCOMP._IOwnership _out579;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out580;
            (this).GenExpr(_2105_expr, selfIdent, _2119_newEnv, expectedOwnership, out _out578, out _out579, out _out580);
            _2120_recGen = _out578;
            _2121_recOwned = _out579;
            _2122_recIdents = _out580;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2122_recIdents, _2110_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2120_recGen));
            RAST._IExpr _out581;
            DCOMP._IOwnership _out582;
            (this).FromOwnership(r, _2121_recOwned, expectedOwnership, out _out581, out _out582);
            r = _out581;
            resultingOwnership = _out582;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2123_name = _source91.dtor_name;
          DAST._IType _2124_tpe = _source91.dtor_typ;
          DAST._IExpression _2125_value = _source91.dtor_value;
          DAST._IExpression _2126_iifeBody = _source91.dtor_iifeBody;
          unmatched91 = false;
          {
            RAST._IExpr _2127_valueGen;
            DCOMP._IOwnership _2128___v211;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2129_recIdents;
            RAST._IExpr _out583;
            DCOMP._IOwnership _out584;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out585;
            (this).GenExpr(_2125_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out583, out _out584, out _out585);
            _2127_valueGen = _out583;
            _2128___v211 = _out584;
            _2129_recIdents = _out585;
            readIdents = _2129_recIdents;
            RAST._IType _2130_valueTypeGen;
            RAST._IType _out586;
            _out586 = (this).GenType(_2124_tpe, DCOMP.GenTypeContext.InFn());
            _2130_valueTypeGen = _out586;
            RAST._IExpr _2131_bodyGen;
            DCOMP._IOwnership _2132___v212;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2133_bodyIdents;
            RAST._IExpr _out587;
            DCOMP._IOwnership _out588;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
            (this).GenExpr(_2126_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out587, out _out588, out _out589);
            _2131_bodyGen = _out587;
            _2132___v212 = _out588;
            _2133_bodyIdents = _out589;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2133_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_2123_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_2123_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_2130_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2127_valueGen))).Then(_2131_bodyGen));
            RAST._IExpr _out590;
            DCOMP._IOwnership _out591;
            (this).FromOwned(r, expectedOwnership, out _out590, out _out591);
            r = _out590;
            resultingOwnership = _out591;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_Apply) {
          DAST._IExpression _2134_func = _source91.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2135_args = _source91.dtor_args;
          unmatched91 = false;
          {
            RAST._IExpr _2136_funcExpr;
            DCOMP._IOwnership _2137___v213;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2138_recIdents;
            RAST._IExpr _out592;
            DCOMP._IOwnership _out593;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
            (this).GenExpr(_2134_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out592, out _out593, out _out594);
            _2136_funcExpr = _out592;
            _2137___v213 = _out593;
            _2138_recIdents = _out594;
            readIdents = _2138_recIdents;
            Dafny.ISequence<RAST._IExpr> _2139_rArgs;
            _2139_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi48 = new BigInteger((_2135_args).Count);
            for (BigInteger _2140_i = BigInteger.Zero; _2140_i < _hi48; _2140_i++) {
              RAST._IExpr _2141_argExpr;
              DCOMP._IOwnership _2142_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2143_argIdents;
              RAST._IExpr _out595;
              DCOMP._IOwnership _out596;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out597;
              (this).GenExpr((_2135_args).Select(_2140_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out595, out _out596, out _out597);
              _2141_argExpr = _out595;
              _2142_argOwned = _out596;
              _2143_argIdents = _out597;
              _2139_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2139_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2141_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2143_argIdents);
            }
            r = (_2136_funcExpr).Apply(_2139_rArgs);
            RAST._IExpr _out598;
            DCOMP._IOwnership _out599;
            (this).FromOwned(r, expectedOwnership, out _out598, out _out599);
            r = _out598;
            resultingOwnership = _out599;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_TypeTest) {
          DAST._IExpression _2144_on = _source91.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2145_dType = _source91.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2146_variant = _source91.dtor_variant;
          unmatched91 = false;
          {
            RAST._IExpr _2147_exprGen;
            DCOMP._IOwnership _2148___v214;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2149_recIdents;
            RAST._IExpr _out600;
            DCOMP._IOwnership _out601;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out602;
            (this).GenExpr(_2144_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out600, out _out601, out _out602);
            _2147_exprGen = _out600;
            _2148___v214 = _out601;
            _2149_recIdents = _out602;
            RAST._IType _2150_dTypePath;
            RAST._IType _out603;
            _out603 = DCOMP.COMP.GenPath(_2145_dType);
            _2150_dTypePath = _out603;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2147_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2150_dTypePath).MSel(DCOMP.__default.escapeName(_2146_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out604;
            DCOMP._IOwnership _out605;
            (this).FromOwned(r, expectedOwnership, out _out604, out _out605);
            r = _out604;
            resultingOwnership = _out605;
            readIdents = _2149_recIdents;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_BoolBoundedPool) {
          unmatched91 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out606;
            DCOMP._IOwnership _out607;
            (this).FromOwned(r, expectedOwnership, out _out606, out _out607);
            r = _out606;
            resultingOwnership = _out607;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_SetBoundedPool) {
          DAST._IExpression _2151_of = _source91.dtor_of;
          unmatched91 = false;
          {
            RAST._IExpr _2152_exprGen;
            DCOMP._IOwnership _2153___v215;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2154_recIdents;
            RAST._IExpr _out608;
            DCOMP._IOwnership _out609;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
            (this).GenExpr(_2151_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out608, out _out609, out _out610);
            _2152_exprGen = _out608;
            _2153___v215 = _out609;
            _2154_recIdents = _out610;
            r = ((_2152_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out611;
            DCOMP._IOwnership _out612;
            (this).FromOwned(r, expectedOwnership, out _out611, out _out612);
            r = _out611;
            resultingOwnership = _out612;
            readIdents = _2154_recIdents;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_SeqBoundedPool) {
          DAST._IExpression _2155_of = _source91.dtor_of;
          bool _2156_includeDuplicates = _source91.dtor_includeDuplicates;
          unmatched91 = false;
          {
            RAST._IExpr _2157_exprGen;
            DCOMP._IOwnership _2158___v216;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2159_recIdents;
            RAST._IExpr _out613;
            DCOMP._IOwnership _out614;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out615;
            (this).GenExpr(_2155_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out613, out _out614, out _out615);
            _2157_exprGen = _out613;
            _2158___v216 = _out614;
            _2159_recIdents = _out615;
            r = ((_2157_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2156_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out616;
            DCOMP._IOwnership _out617;
            (this).FromOwned(r, expectedOwnership, out _out616, out _out617);
            r = _out616;
            resultingOwnership = _out617;
            readIdents = _2159_recIdents;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_MapBoundedPool) {
          DAST._IExpression _2160_of = _source91.dtor_of;
          unmatched91 = false;
          {
            RAST._IExpr _2161_exprGen;
            DCOMP._IOwnership _2162___v217;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2163_recIdents;
            RAST._IExpr _out618;
            DCOMP._IOwnership _out619;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out620;
            (this).GenExpr(_2160_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out618, out _out619, out _out620);
            _2161_exprGen = _out618;
            _2162___v217 = _out619;
            _2163_recIdents = _out620;
            r = ((((_2161_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2163_recIdents;
            RAST._IExpr _out621;
            DCOMP._IOwnership _out622;
            (this).FromOwned(r, expectedOwnership, out _out621, out _out622);
            r = _out621;
            resultingOwnership = _out622;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_IntRange) {
          DAST._IExpression _2164_lo = _source91.dtor_lo;
          DAST._IExpression _2165_hi = _source91.dtor_hi;
          bool _2166_up = _source91.dtor_up;
          unmatched91 = false;
          {
            RAST._IExpr _2167_lo;
            DCOMP._IOwnership _2168___v218;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2169_recIdentsLo;
            RAST._IExpr _out623;
            DCOMP._IOwnership _out624;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out625;
            (this).GenExpr(_2164_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out623, out _out624, out _out625);
            _2167_lo = _out623;
            _2168___v218 = _out624;
            _2169_recIdentsLo = _out625;
            RAST._IExpr _2170_hi;
            DCOMP._IOwnership _2171___v219;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2172_recIdentsHi;
            RAST._IExpr _out626;
            DCOMP._IOwnership _out627;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out628;
            (this).GenExpr(_2165_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out626, out _out627, out _out628);
            _2170_hi = _out626;
            _2171___v219 = _out627;
            _2172_recIdentsHi = _out628;
            if (_2166_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2167_lo, _2170_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2170_hi, _2167_lo));
            }
            RAST._IExpr _out629;
            DCOMP._IOwnership _out630;
            (this).FromOwned(r, expectedOwnership, out _out629, out _out630);
            r = _out629;
            resultingOwnership = _out630;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2169_recIdentsLo, _2172_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_UnboundedIntRange) {
          DAST._IExpression _2173_start = _source91.dtor_start;
          bool _2174_up = _source91.dtor_up;
          unmatched91 = false;
          {
            RAST._IExpr _2175_start;
            DCOMP._IOwnership _2176___v220;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2177_recIdentStart;
            RAST._IExpr _out631;
            DCOMP._IOwnership _out632;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out633;
            (this).GenExpr(_2173_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out631, out _out632, out _out633);
            _2175_start = _out631;
            _2176___v220 = _out632;
            _2177_recIdentStart = _out633;
            if (_2174_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2175_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2175_start);
            }
            RAST._IExpr _out634;
            DCOMP._IOwnership _out635;
            (this).FromOwned(r, expectedOwnership, out _out634, out _out635);
            r = _out634;
            resultingOwnership = _out635;
            readIdents = _2177_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched91) {
        if (_source91.is_MapBuilder) {
          DAST._IType _2178_keyType = _source91.dtor_keyType;
          DAST._IType _2179_valueType = _source91.dtor_valueType;
          unmatched91 = false;
          {
            RAST._IType _2180_kType;
            RAST._IType _out636;
            _out636 = (this).GenType(_2178_keyType, DCOMP.GenTypeContext.@default());
            _2180_kType = _out636;
            RAST._IType _2181_vType;
            RAST._IType _out637;
            _out637 = (this).GenType(_2179_valueType, DCOMP.GenTypeContext.@default());
            _2181_vType = _out637;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2180_kType, _2181_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
      if (unmatched91) {
        if (_source91.is_SetBuilder) {
          DAST._IType _2182_elemType = _source91.dtor_elemType;
          unmatched91 = false;
          {
            RAST._IType _2183_eType;
            RAST._IType _out640;
            _out640 = (this).GenType(_2182_elemType, DCOMP.GenTypeContext.@default());
            _2183_eType = _out640;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2183_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out641;
            DCOMP._IOwnership _out642;
            (this).FromOwned(r, expectedOwnership, out _out641, out _out642);
            r = _out641;
            resultingOwnership = _out642;
            return ;
          }
        }
      }
      if (unmatched91) {
        DAST._IType _2184_elemType = _source91.dtor_elemType;
        DAST._IExpression _2185_collection = _source91.dtor_collection;
        bool _2186_is__forall = _source91.dtor_is__forall;
        DAST._IExpression _2187_lambda = _source91.dtor_lambda;
        unmatched91 = false;
        {
          RAST._IType _2188_tpe;
          RAST._IType _out643;
          _out643 = (this).GenType(_2184_elemType, DCOMP.GenTypeContext.@default());
          _2188_tpe = _out643;
          RAST._IExpr _2189_collectionGen;
          DCOMP._IOwnership _2190___v221;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2191_recIdents;
          RAST._IExpr _out644;
          DCOMP._IOwnership _out645;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out646;
          (this).GenExpr(_2185_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out644, out _out645, out _out646);
          _2189_collectionGen = _out644;
          _2190___v221 = _out645;
          _2191_recIdents = _out646;
          Dafny.ISequence<DAST._IAttribute> _2192_extraAttributes;
          _2192_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2185_collection).is_IntRange) || ((_2185_collection).is_UnboundedIntRange)) || ((_2185_collection).is_SeqBoundedPool)) {
            _2192_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2187_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2193_formals;
            _2193_formals = (_2187_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2194_newFormals;
            _2194_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi49 = new BigInteger((_2193_formals).Count);
            for (BigInteger _2195_i = BigInteger.Zero; _2195_i < _hi49; _2195_i++) {
              var _pat_let_tv111 = _2192_extraAttributes;
              var _pat_let_tv112 = _2193_formals;
              _2194_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2194_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2193_formals).Select(_2195_i), _pat_let36_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let36_0, _2196_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv111, ((_pat_let_tv112).Select(_2195_i)).dtor_attributes), _pat_let37_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let37_0, _2197_dt__update_hattributes_h0 => DAST.Formal.create((_2196_dt__update__tmp_h0).dtor_name, (_2196_dt__update__tmp_h0).dtor_typ, _2197_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv113 = _2194_newFormals;
            DAST._IExpression _2198_newLambda;
            _2198_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2187_lambda, _pat_let38_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let38_0, _2199_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv113, _pat_let39_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let39_0, _2200_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2200_dt__update_hparams_h0, (_2199_dt__update__tmp_h1).dtor_retType, (_2199_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2201_lambdaGen;
            DCOMP._IOwnership _2202___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2203_recLambdaIdents;
            RAST._IExpr _out647;
            DCOMP._IOwnership _out648;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out649;
            (this).GenExpr(_2198_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out647, out _out648, out _out649);
            _2201_lambdaGen = _out647;
            _2202___v222 = _out648;
            _2203_recLambdaIdents = _out649;
            Dafny.ISequence<Dafny.Rune> _2204_fn;
            _2204_fn = ((_2186_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2189_collectionGen).Sel(_2204_fn)).Apply1(((_2201_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2191_recIdents, _2203_recLambdaIdents);
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Quantifier without an inline lambda"));
            r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
          RAST._IExpr _out650;
          DCOMP._IOwnership _out651;
          (this).FromOwned(r, expectedOwnership, out _out650, out _out651);
          r = _out650;
          resultingOwnership = _out651;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _2205_i;
      _2205_i = BigInteger.Zero;
      while ((_2205_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2206_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _2207_m;
        RAST._IMod _out652;
        _out652 = (this).GenModule((p).Select(_2205_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2207_m = _out652;
        _2206_generated = (_2207_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_2205_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2206_generated);
        _2205_i = (_2205_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2208_i;
      _2208_i = BigInteger.Zero;
      while ((_2208_i) < (new BigInteger((fullName).Count))) {
        if ((_2208_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2208_i)));
        _2208_i = (_2208_i) + (BigInteger.One);
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
    public static Dafny.IMap<DAST._IBinOp,Dafny.ISequence<Dafny.Rune>> OpTable { get {
      return Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.FromElements(new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Mod(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("%")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_And(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Or(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("||")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Div(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Lt(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_LtChar(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Plus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("+")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Minus(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("-")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_Times(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseAnd(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseOr(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("|")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseXor(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("^")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftRight(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">>")), new Dafny.Pair<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>(DAST.BinOp.create_BitwiseShiftLeft(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<<")));
    } }
  }
} // end of namespace DCOMP