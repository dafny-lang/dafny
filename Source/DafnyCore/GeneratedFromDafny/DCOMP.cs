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
        Std.Wrappers._IOption<DAST._IResolvedType> _1068_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source47 = (rs).Select(BigInteger.Zero);
          bool unmatched47 = true;
          if (unmatched47) {
            if (_source47.is_UserDefined) {
              DAST._IResolvedType _1069_resolvedType = _source47.dtor_resolved;
              unmatched47 = false;
              return DCOMP.__default.TraitTypeContainingMethod(_1069_resolvedType, _pat_let_tv104);
            }
          }
          if (unmatched47) {
            DAST._IType _1070___v44 = _source47;
            unmatched47 = false;
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
          throw new System.Exception("unexpected control point");
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source48 = _1068_res;
        bool unmatched48 = true;
        if (unmatched48) {
          if (_source48.is_Some) {
            DAST._IResolvedType _1071___v45 = _source48.dtor_value;
            unmatched48 = false;
            return _1068_res;
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
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1072_path = _let_tmp_rhs52.dtor_path;
      Dafny.ISequence<DAST._IType> _1073_typeArgs = _let_tmp_rhs52.dtor_typeArgs;
      DAST._IResolvedTypeBase _1074_kind = _let_tmp_rhs52.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1075_attributes = _let_tmp_rhs52.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1076_properMethods = _let_tmp_rhs52.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1077_extendedTypes = _let_tmp_rhs52.dtor_extendedTypes;
      if ((_1076_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1077_extendedTypes, dafnyName);
      }
    }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("async"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("await"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("break"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("const"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("continue"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("crate"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("else"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("enum"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("for"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("if"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("impl"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("loop"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("match"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mod"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("mut"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("pub"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ref"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("return"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("static"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("struct"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("super"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("trait"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("union"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsafe"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("use"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("where"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("while"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Keywords"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("The"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("abstract"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("become"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("box"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("do"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("final"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("macro"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("override"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("priv"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("try"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("typeof"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unsized"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("virtual"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("yield"));
    } }
    public static Dafny.ISet<Dafny.ISequence<Dafny.Rune>> reserved__rust__need__prefix { get {
      return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u8"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u16"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u32"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u64"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("u128"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i8"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i16"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i32"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i64"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("i128"));
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
      BigInteger _1078_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1078_indexInEnv), ((this).dtor_names).Drop((_1078_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _1079_modName;
      _1079_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1079_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1080_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1080_body = _out15;
        s = RAST.Mod.create_Mod(_1079_modName, _1080_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _1081_i = BigInteger.Zero; _1081_i < _hi5; _1081_i++) {
        Dafny.ISequence<RAST._IModDecl> _1082_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source49 = (body).Select(_1081_i);
        bool unmatched49 = true;
        if (unmatched49) {
          if (_source49.is_Module) {
            DAST._IModule _1083_m = _source49.dtor_Module_a0;
            unmatched49 = false;
            RAST._IMod _1084_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1083_m, containingPath);
            _1084_mm = _out16;
            _1082_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1084_mm));
          }
        }
        if (unmatched49) {
          if (_source49.is_Class) {
            DAST._IClass _1085_c = _source49.dtor_Class_a0;
            unmatched49 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1085_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1085_c).dtor_name)));
            _1082_generated = _out17;
          }
        }
        if (unmatched49) {
          if (_source49.is_Trait) {
            DAST._ITrait _1086_t = _source49.dtor_Trait_a0;
            unmatched49 = false;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenTrait(_1086_t, containingPath);
            _1082_generated = _out18;
          }
        }
        if (unmatched49) {
          if (_source49.is_Newtype) {
            DAST._INewtype _1087_n = _source49.dtor_Newtype_a0;
            unmatched49 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1087_n);
            _1082_generated = _out19;
          }
        }
        if (unmatched49) {
          if (_source49.is_SynonymType) {
            DAST._ISynonymType _1088_s = _source49.dtor_SynonymType_a0;
            unmatched49 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1088_s);
            _1082_generated = _out20;
          }
        }
        if (unmatched49) {
          DAST._IDatatype _1089_d = _source49.dtor_Datatype_a0;
          unmatched49 = false;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1089_d);
          _1082_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1082_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1090_genTpConstraint;
      _1090_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1090_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1090_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1090_genTpConstraint);
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
        for (BigInteger _1091_tpI = BigInteger.Zero; _1091_tpI < _hi6; _1091_tpI++) {
          DAST._ITypeArgDecl _1092_tp;
          _1092_tp = (@params).Select(_1091_tpI);
          DAST._IType _1093_typeArg;
          RAST._ITypeParamDecl _1094_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1092_tp, out _out22, out _out23);
          _1093_typeArg = _out22;
          _1094_typeParam = _out23;
          RAST._IType _1095_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1093_typeArg, DCOMP.GenTypeContext.@default());
          _1095_rType = _out24;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1093_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1095_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1094_typeParam));
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
      Dafny.ISequence<DAST._IType> _1096_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1097_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1098_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1099_whereConstraints;
      Dafny.ISequence<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1096_typeParamsSeq = _out25;
      _1097_rTypeParams = _out26;
      _1098_rTypeParamsDecls = _out27;
      _1099_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1100_constrainedTypeParams;
      _1100_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1098_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1101_fields;
      _1101_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1102_fieldInits;
      _1102_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1103_fieldI = BigInteger.Zero; _1103_fieldI < _hi7; _1103_fieldI++) {
        DAST._IField _1104_field;
        _1104_field = ((c).dtor_fields).Select(_1103_fieldI);
        RAST._IType _1105_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1104_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1105_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1106_fieldRustName;
        _1106_fieldRustName = DCOMP.__default.escapeName(((_1104_field).dtor_formal).dtor_name);
        _1101_fields = Dafny.Sequence<RAST._IField>.Concat(_1101_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1106_fieldRustName, _1105_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source50 = (_1104_field).dtor_defaultValue;
        bool unmatched50 = true;
        if (unmatched50) {
          if (_source50.is_Some) {
            DAST._IExpression _1107_e = _source50.dtor_value;
            unmatched50 = false;
            {
              RAST._IExpr _1108_expr;
              DCOMP._IOwnership _1109___v46;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1110___v47;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1107_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1108_expr = _out30;
              _1109___v46 = _out31;
              _1110___v47 = _out32;
              _1102_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1102_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1106_fieldRustName, _1108_expr)));
            }
          }
        }
        if (unmatched50) {
          unmatched50 = false;
          {
            RAST._IExpr _1111_default;
            _1111_default = RAST.__default.std__Default__default;
            if ((_1105_fieldType).IsObjectOrPointer()) {
              _1111_default = (_1105_fieldType).ToNullExpr();
            }
            _1102_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1102_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1106_fieldRustName, _1111_default)));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1112_typeParamI = BigInteger.Zero; _1112_typeParamI < _hi8; _1112_typeParamI++) {
        DAST._IType _1113_typeArg;
        RAST._ITypeParamDecl _1114_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1112_typeParamI), out _out33, out _out34);
        _1113_typeArg = _out33;
        _1114_typeParam = _out34;
        RAST._IType _1115_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1113_typeArg, DCOMP.GenTypeContext.@default());
        _1115_rTypeArg = _out35;
        _1101_fields = Dafny.Sequence<RAST._IField>.Concat(_1101_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1112_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1115_rTypeArg))))));
        _1102_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1102_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1112_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1116_datatypeName;
      _1116_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1117_struct;
      _1117_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1116_datatypeName, _1098_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1101_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1117_struct));
      Dafny.ISequence<RAST._IImplMember> _1118_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1119_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1096_typeParamsSeq, out _out36, out _out37);
      _1118_implBodyRaw = _out36;
      _1119_traitBodies = _out37;
      Dafny.ISequence<RAST._IImplMember> _1120_implBody;
      _1120_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.Type.create_SelfOwned())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel((this).allocate)).ApplyType1(RAST.Type.create_SelfOwned())).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1118_implBodyRaw);
      RAST._IImpl _1121_i;
      _1121_i = RAST.Impl.create_Impl(_1098_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1116_datatypeName), _1097_rTypeParams), _1099_whereConstraints, _1120_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1121_i)));
      RAST._IType _1122_genSelfPath;
      RAST._IType _out38;
      _out38 = DCOMP.COMP.GenPath(path);
      _1122_genSelfPath = _out38;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1098_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"))))), RAST.Type.create_TypeApp(_1122_genSelfPath, _1097_rTypeParams), _1099_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any")))))))))));
      BigInteger _hi9 = new BigInteger(((c).dtor_superClasses).Count);
      for (BigInteger _1123_i = BigInteger.Zero; _1123_i < _hi9; _1123_i++) {
        DAST._IType _1124_superClass;
        _1124_superClass = ((c).dtor_superClasses).Select(_1123_i);
        DAST._IType _source51 = _1124_superClass;
        bool unmatched51 = true;
        if (unmatched51) {
          if (_source51.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source51.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1125_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1126_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<DAST._IAttribute> _1127___v48 = resolved0.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1128___v49 = resolved0.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1129___v50 = resolved0.dtor_extendedTypes;
              unmatched51 = false;
              {
                RAST._IType _1130_pathStr;
                RAST._IType _out39;
                _out39 = DCOMP.COMP.GenPath(_1125_traitPath);
                _1130_pathStr = _out39;
                Dafny.ISequence<RAST._IType> _1131_typeArgs;
                Dafny.ISequence<RAST._IType> _out40;
                _out40 = (this).GenTypeArgs(_1126_typeArgs, DCOMP.GenTypeContext.@default());
                _1131_typeArgs = _out40;
                Dafny.ISequence<RAST._IImplMember> _1132_body;
                _1132_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1119_traitBodies).Contains(_1125_traitPath)) {
                  _1132_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1119_traitBodies,_1125_traitPath);
                }
                RAST._IType _1133_traitType;
                _1133_traitType = RAST.Type.create_TypeApp(_1130_pathStr, _1131_typeArgs);
                RAST._IModDecl _1134_x;
                _1134_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1098_rTypeParamsDecls, _1133_traitType, RAST.Type.create_TypeApp(_1122_genSelfPath, _1097_rTypeParams), _1099_whereConstraints, _1132_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1134_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1098_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1133_traitType))), RAST.Type.create_TypeApp(_1122_genSelfPath, _1097_rTypeParams), _1099_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1133_traitType)))))))));
              }
            }
          }
        }
        if (unmatched51) {
          DAST._IType _1135___v51 = _source51;
          unmatched51 = false;
        }
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1136_typeParamsSeq;
      _1136_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1137_typeParamDecls;
      _1137_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1138_typeParams;
      _1138_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi10 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1139_tpI = BigInteger.Zero; _1139_tpI < _hi10; _1139_tpI++) {
          DAST._ITypeArgDecl _1140_tp;
          _1140_tp = ((t).dtor_typeParams).Select(_1139_tpI);
          DAST._IType _1141_typeArg;
          RAST._ITypeParamDecl _1142_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1140_tp, out _out41, out _out42);
          _1141_typeArg = _out41;
          _1142_typeParamDecl = _out42;
          _1136_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1136_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1141_typeArg));
          _1137_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1137_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1142_typeParamDecl));
          RAST._IType _1143_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1141_typeArg, DCOMP.GenTypeContext.@default());
          _1143_typeParam = _out43;
          _1138_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1138_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1143_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1144_fullPath;
      _1144_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1145_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1146___v52;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1144_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1136_typeParamsSeq, out _out44, out _out45);
      _1145_implBody = _out44;
      _1146___v52 = _out45;
      Dafny.ISequence<RAST._IType> _1147_parents;
      _1147_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi11 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1148_i = BigInteger.Zero; _1148_i < _hi11; _1148_i++) {
        RAST._IType _1149_tpe;
        RAST._IType _out46;
        _out46 = (this).GenType(((t).dtor_parents).Select(_1148_i), DCOMP.GenTypeContext.ForTraitParents());
        _1149_tpe = _out46;
        _1147_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1147_parents, Dafny.Sequence<RAST._IType>.FromElements(_1149_tpe)), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply1(RAST.Type.create_DynType(_1149_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1137_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1138_typeParams), _1147_parents, _1145_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1150_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1151_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1152_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1153_whereConstraints;
      Dafny.ISequence<DAST._IType> _out47;
      Dafny.ISequence<RAST._IType> _out48;
      Dafny.ISequence<RAST._ITypeParamDecl> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1150_typeParamsSeq = _out47;
      _1151_rTypeParams = _out48;
      _1152_rTypeParamsDecls = _out49;
      _1153_whereConstraints = _out50;
      Dafny.ISequence<Dafny.Rune> _1154_constrainedTypeParams;
      _1154_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1152_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1155_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source52 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched52 = true;
      if (unmatched52) {
        if (_source52.is_Some) {
          RAST._IType _1156_v = _source52.dtor_value;
          unmatched52 = false;
          _1155_underlyingType = _1156_v;
        }
      }
      if (unmatched52) {
        unmatched52 = false;
        RAST._IType _out51;
        _out51 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1155_underlyingType = _out51;
      }
      DAST._IType _1157_resultingType;
      _1157_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1158_newtypeName;
      _1158_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1158_newtypeName, _1152_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1155_underlyingType))))));
      RAST._IExpr _1159_fnBody;
      _1159_fnBody = RAST.Expr.create_Identifier(_1158_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source53 = (c).dtor_witnessExpr;
      bool unmatched53 = true;
      if (unmatched53) {
        if (_source53.is_Some) {
          DAST._IExpression _1160_e = _source53.dtor_value;
          unmatched53 = false;
          {
            DAST._IExpression _1161_e;
            _1161_e = ((object.Equals((c).dtor_base, _1157_resultingType)) ? (_1160_e) : (DAST.Expression.create_Convert(_1160_e, (c).dtor_base, _1157_resultingType)));
            RAST._IExpr _1162_eStr;
            DCOMP._IOwnership _1163___v53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1164___v54;
            RAST._IExpr _out52;
            DCOMP._IOwnership _out53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out54;
            (this).GenExpr(_1161_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out52, out _out53, out _out54);
            _1162_eStr = _out52;
            _1163___v53 = _out53;
            _1164___v54 = _out54;
            _1159_fnBody = (_1159_fnBody).Apply1(_1162_eStr);
          }
        }
      }
      if (unmatched53) {
        unmatched53 = false;
        {
          _1159_fnBody = (_1159_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1165_body;
      _1165_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1159_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source54 = (c).dtor_constraint;
      bool unmatched54 = true;
      if (unmatched54) {
        if (_source54.is_None) {
          unmatched54 = false;
        }
      }
      if (unmatched54) {
        DAST._INewtypeConstraint value8 = _source54.dtor_value;
        DAST._IFormal _1166_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1167_constraintStmts = value8.dtor_constraintStmts;
        unmatched54 = false;
        RAST._IExpr _1168_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1169___v55;
        DCOMP._IEnvironment _1170_newEnv;
        RAST._IExpr _out55;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out56;
        DCOMP._IEnvironment _out57;
        (this).GenStmts(_1167_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out55, out _out56, out _out57);
        _1168_rStmts = _out55;
        _1169___v55 = _out56;
        _1170_newEnv = _out57;
        Dafny.ISequence<RAST._IFormal> _1171_rFormals;
        Dafny.ISequence<RAST._IFormal> _out58;
        _out58 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1166_formal));
        _1171_rFormals = _out58;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1152_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1158_newtypeName), _1151_rTypeParams), _1153_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1171_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1168_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1152_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1158_newtypeName), _1151_rTypeParams), _1153_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1165_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1152_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1158_newtypeName), _1151_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1152_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1158_newtypeName), _1151_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1155_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1172_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1173_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1174_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1175_whereConstraints;
      Dafny.ISequence<DAST._IType> _out59;
      Dafny.ISequence<RAST._IType> _out60;
      Dafny.ISequence<RAST._ITypeParamDecl> _out61;
      Dafny.ISequence<Dafny.Rune> _out62;
      (this).GenTypeParameters((c).dtor_typeParams, out _out59, out _out60, out _out61, out _out62);
      _1172_typeParamsSeq = _out59;
      _1173_rTypeParams = _out60;
      _1174_rTypeParamsDecls = _out61;
      _1175_whereConstraints = _out62;
      Dafny.ISequence<Dafny.Rune> _1176_constrainedTypeParams;
      _1176_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1174_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _1177_synonymTypeName;
      _1177_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1178_resultingType;
      RAST._IType _out63;
      _out63 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1178_resultingType = _out63;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1177_synonymTypeName, _1174_rTypeParamsDecls, _1178_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source55 = (c).dtor_witnessExpr;
      bool unmatched55 = true;
      if (unmatched55) {
        if (_source55.is_Some) {
          DAST._IExpression _1179_e = _source55.dtor_value;
          unmatched55 = false;
          {
            RAST._IExpr _1180_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1181___v56;
            DCOMP._IEnvironment _1182_newEnv;
            RAST._IExpr _out64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out65;
            DCOMP._IEnvironment _out66;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out64, out _out65, out _out66);
            _1180_rStmts = _out64;
            _1181___v56 = _out65;
            _1182_newEnv = _out66;
            RAST._IExpr _1183_rExpr;
            DCOMP._IOwnership _1184___v57;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1185___v58;
            RAST._IExpr _out67;
            DCOMP._IOwnership _out68;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out69;
            (this).GenExpr(_1179_e, DCOMP.SelfInfo.create_NoSelf(), _1182_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out67, out _out68, out _out69);
            _1183_rExpr = _out67;
            _1184___v57 = _out68;
            _1185___v58 = _out69;
            Dafny.ISequence<Dafny.Rune> _1186_constantName;
            _1186_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1186_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1178_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1180_rStmts).Then(_1183_rExpr)))))));
          }
        }
      }
      if (unmatched55) {
        unmatched55 = false;
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1187_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1188_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1189_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1190_whereConstraints;
      Dafny.ISequence<DAST._IType> _out70;
      Dafny.ISequence<RAST._IType> _out71;
      Dafny.ISequence<RAST._ITypeParamDecl> _out72;
      Dafny.ISequence<Dafny.Rune> _out73;
      (this).GenTypeParameters((c).dtor_typeParams, out _out70, out _out71, out _out72, out _out73);
      _1187_typeParamsSeq = _out70;
      _1188_rTypeParams = _out71;
      _1189_rTypeParamsDecls = _out72;
      _1190_whereConstraints = _out73;
      Dafny.ISequence<Dafny.Rune> _1191_datatypeName;
      _1191_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1192_ctors;
      _1192_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      BigInteger _hi12 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1193_i = BigInteger.Zero; _1193_i < _hi12; _1193_i++) {
        DAST._IDatatypeCtor _1194_ctor;
        _1194_ctor = ((c).dtor_ctors).Select(_1193_i);
        Dafny.ISequence<RAST._IField> _1195_ctorArgs;
        _1195_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1196_isNumeric;
        _1196_isNumeric = false;
        BigInteger _hi13 = new BigInteger(((_1194_ctor).dtor_args).Count);
        for (BigInteger _1197_j = BigInteger.Zero; _1197_j < _hi13; _1197_j++) {
          DAST._IDatatypeDtor _1198_dtor;
          _1198_dtor = ((_1194_ctor).dtor_args).Select(_1197_j);
          RAST._IType _1199_formalType;
          RAST._IType _out74;
          _out74 = (this).GenType(((_1198_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1199_formalType = _out74;
          Dafny.ISequence<Dafny.Rune> _1200_formalName;
          _1200_formalName = DCOMP.__default.escapeName(((_1198_dtor).dtor_formal).dtor_name);
          if (((_1197_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1200_formalName))) {
            _1196_isNumeric = true;
          }
          if ((((_1197_j).Sign != 0) && (_1196_isNumeric)) && (!(Std.Strings.__default.OfNat(_1197_j)).Equals(_1200_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1200_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1197_j)));
            _1196_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1195_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1195_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1200_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1199_formalType))))));
          } else {
            _1195_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1195_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1200_formalName, _1199_formalType))));
          }
        }
        RAST._IFields _1201_namedFields;
        _1201_namedFields = RAST.Fields.create_NamedFields(_1195_ctorArgs);
        if (_1196_isNumeric) {
          _1201_namedFields = (_1201_namedFields).ToNamelessFields();
        }
        _1192_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1192_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1194_ctor).dtor_name), _1201_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1202_selfPath;
      _1202_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1203_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1204_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out75;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out76;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1202_selfPath, _1187_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1187_typeParamsSeq, out _out75, out _out76);
      _1203_implBodyRaw = _out75;
      _1204_traitBodies = _out76;
      Dafny.ISequence<RAST._IImplMember> _1205_implBody;
      _1205_implBody = _1203_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1206_emittedFields;
      _1206_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi14 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1207_i = BigInteger.Zero; _1207_i < _hi14; _1207_i++) {
        DAST._IDatatypeCtor _1208_ctor;
        _1208_ctor = ((c).dtor_ctors).Select(_1207_i);
        BigInteger _hi15 = new BigInteger(((_1208_ctor).dtor_args).Count);
        for (BigInteger _1209_j = BigInteger.Zero; _1209_j < _hi15; _1209_j++) {
          DAST._IDatatypeDtor _1210_dtor;
          _1210_dtor = ((_1208_ctor).dtor_args).Select(_1209_j);
          Dafny.ISequence<Dafny.Rune> _1211_callName;
          _1211_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1210_dtor).dtor_callName, DCOMP.__default.escapeName(((_1210_dtor).dtor_formal).dtor_name));
          if (!((_1206_emittedFields).Contains(_1211_callName))) {
            _1206_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1206_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1211_callName));
            RAST._IType _1212_formalType;
            RAST._IType _out77;
            _out77 = (this).GenType(((_1210_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1212_formalType = _out77;
            Dafny.ISequence<RAST._IMatchCase> _1213_cases;
            _1213_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1214_k = BigInteger.Zero; _1214_k < _hi16; _1214_k++) {
              DAST._IDatatypeCtor _1215_ctor2;
              _1215_ctor2 = ((c).dtor_ctors).Select(_1214_k);
              Dafny.ISequence<Dafny.Rune> _1216_pattern;
              _1216_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1191_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1215_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1217_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1218_hasMatchingField;
              _1218_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1219_patternInner;
              _1219_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1220_isNumeric;
              _1220_isNumeric = false;
              BigInteger _hi17 = new BigInteger(((_1215_ctor2).dtor_args).Count);
              for (BigInteger _1221_l = BigInteger.Zero; _1221_l < _hi17; _1221_l++) {
                DAST._IDatatypeDtor _1222_dtor2;
                _1222_dtor2 = ((_1215_ctor2).dtor_args).Select(_1221_l);
                Dafny.ISequence<Dafny.Rune> _1223_patternName;
                _1223_patternName = DCOMP.__default.escapeName(((_1222_dtor2).dtor_formal).dtor_name);
                if (((_1221_l).Sign == 0) && ((_1223_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1220_isNumeric = true;
                }
                if (_1220_isNumeric) {
                  _1223_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1222_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1221_l)));
                }
                if (object.Equals(((_1210_dtor).dtor_formal).dtor_name, ((_1222_dtor2).dtor_formal).dtor_name)) {
                  _1218_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1223_patternName);
                }
                _1219_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1219_patternInner, _1223_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1220_isNumeric) {
                _1216_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1216_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1219_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1216_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1216_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1219_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1218_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1217_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1218_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1217_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1218_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1217_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1224_ctorMatch;
              _1224_ctorMatch = RAST.MatchCase.create(_1216_pattern, RAST.Expr.create_RawExpr(_1217_rhs));
              _1213_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1213_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1224_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1213_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1213_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1191_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1225_methodBody;
            _1225_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1213_cases);
            _1205_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1205_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1211_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1212_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1225_methodBody)))));
          }
        }
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1226_types;
        _1226_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi18 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1227_typeI = BigInteger.Zero; _1227_typeI < _hi18; _1227_typeI++) {
          DAST._IType _1228_typeArg;
          RAST._ITypeParamDecl _1229_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(((c).dtor_typeParams).Select(_1227_typeI), out _out78, out _out79);
          _1228_typeArg = _out78;
          _1229_rTypeParamDecl = _out79;
          RAST._IType _1230_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1228_typeArg, DCOMP.GenTypeContext.@default());
          _1230_rTypeArg = _out80;
          _1226_types = Dafny.Sequence<RAST._IType>.Concat(_1226_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1230_rTypeArg))));
        }
        _1192_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1192_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1231_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1231_tpe);
})), _1226_types)))));
      }
      Dafny.ISequence<RAST._IModDecl> _1232_enumBody;
      _1232_enumBody = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]")), _1191_datatypeName, _1189_rTypeParamsDecls, _1192_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1189_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1191_datatypeName), _1188_rTypeParams), _1190_whereConstraints, _1205_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1233_printImplBodyCases;
      _1233_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1234_hashImplBodyCases;
      _1234_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi19 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1235_i = BigInteger.Zero; _1235_i < _hi19; _1235_i++) {
        DAST._IDatatypeCtor _1236_ctor;
        _1236_ctor = ((c).dtor_ctors).Select(_1235_i);
        Dafny.ISequence<Dafny.Rune> _1237_ctorMatch;
        _1237_ctorMatch = DCOMP.__default.escapeName((_1236_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1238_modulePrefix;
        _1238_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1239_ctorName;
        _1239_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1238_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1236_ctor).dtor_name));
        if (((new BigInteger((_1239_ctorName).Count)) >= (new BigInteger(13))) && (((_1239_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1239_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1240_printRhs;
        _1240_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1239_ctorName), (((_1236_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1241_hashRhs;
        _1241_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        bool _1242_isNumeric;
        _1242_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1243_ctorMatchInner;
        _1243_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi20 = new BigInteger(((_1236_ctor).dtor_args).Count);
        for (BigInteger _1244_j = BigInteger.Zero; _1244_j < _hi20; _1244_j++) {
          DAST._IDatatypeDtor _1245_dtor;
          _1245_dtor = ((_1236_ctor).dtor_args).Select(_1244_j);
          Dafny.ISequence<Dafny.Rune> _1246_patternName;
          _1246_patternName = DCOMP.__default.escapeName(((_1245_dtor).dtor_formal).dtor_name);
          if (((_1244_j).Sign == 0) && ((_1246_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1242_isNumeric = true;
          }
          if (_1242_isNumeric) {
            _1246_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1245_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1244_j)));
          }
          _1241_hashRhs = (_1241_hashRhs).Then(((RAST.Expr.create_Identifier(_1246_patternName)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          _1243_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1243_ctorMatchInner, _1246_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1244_j).Sign == 1) {
            _1240_printRhs = (_1240_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1240_printRhs = (_1240_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1246_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))));
        }
        if (_1242_isNumeric) {
          _1237_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1237_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1243_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1237_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1237_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1243_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1236_ctor).dtor_hasAnyArgs) {
          _1240_printRhs = (_1240_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1240_printRhs = (_1240_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1233_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1233_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1191_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1237_ctorMatch), RAST.Expr.create_Block(_1240_printRhs))));
        _1234_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1234_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1191_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1237_ctorMatch), RAST.Expr.create_Block(_1241_hashRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        _1233_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1233_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1191_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
        _1234_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1234_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1191_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}")))));
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1247_defaultConstrainedTypeParams;
      _1247_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1189_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1248_rTypeParamsDeclsWithEq;
      _1248_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1189_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1249_rTypeParamsDeclsWithHash;
      _1249_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1189_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1250_printImplBody;
      _1250_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1233_printImplBodyCases);
      RAST._IExpr _1251_hashImplBody;
      _1251_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1234_hashImplBodyCases);
      Dafny.ISequence<RAST._IModDecl> _1252_printImpl;
      _1252_printImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1189_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1191_datatypeName), _1188_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1189_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1191_datatypeName), _1188_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1250_printImplBody)))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1248_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1191_datatypeName), _1188_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements())), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1249_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1191_datatypeName), _1188_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1251_hashImplBody)))))));
      Dafny.ISequence<RAST._IModDecl> _1253_defaultImpl;
      _1253_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      Dafny.ISequence<RAST._IModDecl> _1254_asRefImpl;
      _1254_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements();
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1255_structName;
        _1255_structName = (RAST.Expr.create_Identifier(_1191_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1256_structAssignments;
        _1256_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi21 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1257_i = BigInteger.Zero; _1257_i < _hi21; _1257_i++) {
          DAST._IDatatypeDtor _1258_dtor;
          _1258_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1257_i);
          _1256_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1256_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1258_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1259_defaultConstrainedTypeParams;
        _1259_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1189_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1260_fullType;
        _1260_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1191_datatypeName), _1188_rTypeParams);
        _1253_defaultImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1259_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1260_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1260_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1255_structName, _1256_structAssignments))))))));
        _1254_asRefImpl = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1189_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1260_fullType), RAST.Type.create_Borrowed(_1260_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self)))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(Dafny.Sequence<RAST._IModDecl>.Concat(_1232_enumBody, _1252_printImpl), _1253_defaultImpl), _1254_asRefImpl);
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
        for (BigInteger _1261_i = BigInteger.Zero; _1261_i < _hi22; _1261_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1261_i))));
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
        for (BigInteger _1262_i = BigInteger.Zero; _1262_i < _hi23; _1262_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1262_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi24 = new BigInteger((args).Count);
      for (BigInteger _1263_i = BigInteger.Zero; _1263_i < _hi24; _1263_i++) {
        RAST._IType _1264_genTp;
        RAST._IType _out81;
        _out81 = (this).GenType((args).Select(_1263_i), genTypeContext);
        _1264_genTp = _out81;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1264_genTp));
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, DCOMP._IGenTypeContext genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source56 = c;
      bool unmatched56 = true;
      if (unmatched56) {
        if (_source56.is_UserDefined) {
          DAST._IResolvedType _1265_resolved = _source56.dtor_resolved;
          unmatched56 = false;
          {
            RAST._IType _1266_t;
            RAST._IType _out82;
            _out82 = DCOMP.COMP.GenPath((_1265_resolved).dtor_path);
            _1266_t = _out82;
            Dafny.ISequence<RAST._IType> _1267_typeArgs;
            Dafny.ISequence<RAST._IType> _out83;
            _out83 = (this).GenTypeArgs((_1265_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let9_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let9_0, _1268_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let10_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let10_0, _1269_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1268_dt__update__tmp_h0).dtor_inBinding, (_1268_dt__update__tmp_h0).dtor_inFn, _1269_dt__update_hforTraitParents_h0))))));
            _1267_typeArgs = _out83;
            s = RAST.Type.create_TypeApp(_1266_t, _1267_typeArgs);
            DAST._IResolvedTypeBase _source57 = (_1265_resolved).dtor_kind;
            bool unmatched57 = true;
            if (unmatched57) {
              if (_source57.is_Class) {
                unmatched57 = false;
                {
                  s = (this).Object(s);
                }
              }
            }
            if (unmatched57) {
              if (_source57.is_Datatype) {
                unmatched57 = false;
                {
                  if ((this).IsRcWrapped((_1265_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched57) {
              if (_source57.is_Trait) {
                unmatched57 = false;
                {
                  if (((_1265_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched57) {
              DAST._IType _1270_t = _source57.dtor_baseType;
              DAST._INewtypeRange _1271_range = _source57.dtor_range;
              bool _1272_erased = _source57.dtor_erase;
              unmatched57 = false;
              {
                if (_1272_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source58 = DCOMP.COMP.NewtypeToRustType(_1270_t, _1271_range);
                  bool unmatched58 = true;
                  if (unmatched58) {
                    if (_source58.is_Some) {
                      RAST._IType _1273_v = _source58.dtor_value;
                      unmatched58 = false;
                      s = _1273_v;
                    }
                  }
                  if (unmatched58) {
                    unmatched58 = false;
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched56) {
        if (_source56.is_Object) {
          unmatched56 = false;
          {
            s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
            if (!((genTypeContext).dtor_forTraitParents)) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
        }
      }
      if (unmatched56) {
        if (_source56.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1274_types = _source56.dtor_Tuple_a0;
          unmatched56 = false;
          {
            Dafny.ISequence<RAST._IType> _1275_args;
            _1275_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1276_i;
            _1276_i = BigInteger.Zero;
            while ((_1276_i) < (new BigInteger((_1274_types).Count))) {
              RAST._IType _1277_generated;
              RAST._IType _out84;
              _out84 = (this).GenType((_1274_types).Select(_1276_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _1278_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _1279_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1278_dt__update__tmp_h1).dtor_inBinding, (_1278_dt__update__tmp_h1).dtor_inFn, _1279_dt__update_hforTraitParents_h1))))));
              _1277_generated = _out84;
              _1275_args = Dafny.Sequence<RAST._IType>.Concat(_1275_args, Dafny.Sequence<RAST._IType>.FromElements(_1277_generated));
              _1276_i = (_1276_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1274_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1275_args)) : (RAST.__default.SystemTupleType(_1275_args)));
          }
        }
      }
      if (unmatched56) {
        if (_source56.is_Array) {
          DAST._IType _1280_element = _source56.dtor_element;
          BigInteger _1281_dims = _source56.dtor_dims;
          unmatched56 = false;
          {
            if ((_1281_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1282_elem;
              RAST._IType _out85;
              _out85 = (this).GenType(_1280_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _1283_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _1284_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1283_dt__update__tmp_h2).dtor_inBinding, (_1283_dt__update__tmp_h2).dtor_inFn, _1284_dt__update_hforTraitParents_h2))))));
              _1282_elem = _out85;
              if ((_1281_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1282_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1285_n;
                _1285_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1281_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1285_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1282_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched56) {
        if (_source56.is_Seq) {
          DAST._IType _1286_element = _source56.dtor_element;
          unmatched56 = false;
          {
            RAST._IType _1287_elem;
            RAST._IType _out86;
            _out86 = (this).GenType(_1286_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _1288_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _1289_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1288_dt__update__tmp_h3).dtor_inBinding, (_1288_dt__update__tmp_h3).dtor_inFn, _1289_dt__update_hforTraitParents_h3))))));
            _1287_elem = _out86;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1287_elem));
          }
        }
      }
      if (unmatched56) {
        if (_source56.is_Set) {
          DAST._IType _1290_element = _source56.dtor_element;
          unmatched56 = false;
          {
            RAST._IType _1291_elem;
            RAST._IType _out87;
            _out87 = (this).GenType(_1290_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _1292_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _1293_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1292_dt__update__tmp_h4).dtor_inBinding, (_1292_dt__update__tmp_h4).dtor_inFn, _1293_dt__update_hforTraitParents_h4))))));
            _1291_elem = _out87;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1291_elem));
          }
        }
      }
      if (unmatched56) {
        if (_source56.is_Multiset) {
          DAST._IType _1294_element = _source56.dtor_element;
          unmatched56 = false;
          {
            RAST._IType _1295_elem;
            RAST._IType _out88;
            _out88 = (this).GenType(_1294_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _1296_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _1297_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1296_dt__update__tmp_h5).dtor_inBinding, (_1296_dt__update__tmp_h5).dtor_inFn, _1297_dt__update_hforTraitParents_h5))))));
            _1295_elem = _out88;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1295_elem));
          }
        }
      }
      if (unmatched56) {
        if (_source56.is_Map) {
          DAST._IType _1298_key = _source56.dtor_key;
          DAST._IType _1299_value = _source56.dtor_value;
          unmatched56 = false;
          {
            RAST._IType _1300_keyType;
            RAST._IType _out89;
            _out89 = (this).GenType(_1298_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _1301_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _1302_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1301_dt__update__tmp_h6).dtor_inBinding, (_1301_dt__update__tmp_h6).dtor_inFn, _1302_dt__update_hforTraitParents_h6))))));
            _1300_keyType = _out89;
            RAST._IType _1303_valueType;
            RAST._IType _out90;
            _out90 = (this).GenType(_1299_value, genTypeContext);
            _1303_valueType = _out90;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1300_keyType, _1303_valueType));
          }
        }
      }
      if (unmatched56) {
        if (_source56.is_MapBuilder) {
          DAST._IType _1304_key = _source56.dtor_key;
          DAST._IType _1305_value = _source56.dtor_value;
          unmatched56 = false;
          {
            RAST._IType _1306_keyType;
            RAST._IType _out91;
            _out91 = (this).GenType(_1304_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _1307_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _1308_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1307_dt__update__tmp_h7).dtor_inBinding, (_1307_dt__update__tmp_h7).dtor_inFn, _1308_dt__update_hforTraitParents_h7))))));
            _1306_keyType = _out91;
            RAST._IType _1309_valueType;
            RAST._IType _out92;
            _out92 = (this).GenType(_1305_value, genTypeContext);
            _1309_valueType = _out92;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1306_keyType, _1309_valueType));
          }
        }
      }
      if (unmatched56) {
        if (_source56.is_SetBuilder) {
          DAST._IType _1310_elem = _source56.dtor_element;
          unmatched56 = false;
          {
            RAST._IType _1311_elemType;
            RAST._IType _out93;
            _out93 = (this).GenType(_1310_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _1312_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _1313_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1312_dt__update__tmp_h8).dtor_inBinding, (_1312_dt__update__tmp_h8).dtor_inFn, _1313_dt__update_hforTraitParents_h8))))));
            _1311_elemType = _out93;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1311_elemType));
          }
        }
      }
      if (unmatched56) {
        if (_source56.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1314_args = _source56.dtor_args;
          DAST._IType _1315_result = _source56.dtor_result;
          unmatched56 = false;
          {
            Dafny.ISequence<RAST._IType> _1316_argTypes;
            _1316_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1317_i;
            _1317_i = BigInteger.Zero;
            while ((_1317_i) < (new BigInteger((_1314_args).Count))) {
              RAST._IType _1318_generated;
              RAST._IType _out94;
              _out94 = (this).GenType((_1314_args).Select(_1317_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _1319_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _1320_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let29_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let29_0, _1321_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1319_dt__update__tmp_h9).dtor_inBinding, _1321_dt__update_hinFn_h0, _1320_dt__update_hforTraitParents_h9))))))));
              _1318_generated = _out94;
              _1316_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1316_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1318_generated)));
              _1317_i = (_1317_i) + (BigInteger.One);
            }
            RAST._IType _1322_resultType;
            RAST._IType _out95;
            _out95 = (this).GenType(_1315_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1322_resultType = _out95;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1316_argTypes, _1322_resultType)));
          }
        }
      }
      if (unmatched56) {
        if (_source56.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source56.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1323_name = _h90;
          unmatched56 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1323_name));
        }
      }
      if (unmatched56) {
        if (_source56.is_Primitive) {
          DAST._IPrimitive _1324_p = _source56.dtor_Primitive_a0;
          unmatched56 = false;
          {
            DAST._IPrimitive _source59 = _1324_p;
            bool unmatched59 = true;
            if (unmatched59) {
              if (_source59.is_Int) {
                unmatched59 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
              }
            }
            if (unmatched59) {
              if (_source59.is_Real) {
                unmatched59 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
              }
            }
            if (unmatched59) {
              if (_source59.is_String) {
                unmatched59 = false;
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
              }
            }
            if (unmatched59) {
              if (_source59.is_Bool) {
                unmatched59 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched59) {
              unmatched59 = false;
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          }
        }
      }
      if (unmatched56) {
        Dafny.ISequence<Dafny.Rune> _1325_v = _source56.dtor_Passthrough_a0;
        unmatched56 = false;
        s = RAST.__default.RawType(_1325_v);
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
      for (BigInteger _1326_i = BigInteger.Zero; _1326_i < _hi25; _1326_i++) {
        DAST._IMethod _source60 = (body).Select(_1326_i);
        bool unmatched60 = true;
        if (unmatched60) {
          DAST._IMethod _1327_m = _source60;
          unmatched60 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source61 = (_1327_m).dtor_overridingPath;
            bool unmatched61 = true;
            if (unmatched61) {
              if (_source61.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1328_p = _source61.dtor_value;
                unmatched61 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1329_existing;
                  _1329_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1328_p)) {
                    _1329_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1328_p);
                  }
                  if (((new BigInteger(((_1327_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1330_genMethod;
                  RAST._IImplMember _out96;
                  _out96 = (this).GenMethod(_1327_m, true, enclosingType, enclosingTypeParams);
                  _1330_genMethod = _out96;
                  _1329_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1329_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1330_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1328_p, _1329_existing)));
                }
              }
            }
            if (unmatched61) {
              unmatched61 = false;
              {
                RAST._IImplMember _1331_generated;
                RAST._IImplMember _out97;
                _out97 = (this).GenMethod(_1327_m, forTrait, enclosingType, enclosingTypeParams);
                _1331_generated = _out97;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1331_generated));
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
      for (BigInteger _1332_i = BigInteger.Zero; _1332_i < _hi26; _1332_i++) {
        DAST._IFormal _1333_param;
        _1333_param = (@params).Select(_1332_i);
        RAST._IType _1334_paramType;
        RAST._IType _out98;
        _out98 = (this).GenType((_1333_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1334_paramType = _out98;
        if ((!((_1334_paramType).CanReadWithoutClone())) && (!((_1333_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1334_paramType = RAST.Type.create_Borrowed(_1334_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1333_param).dtor_name), _1334_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1335_params;
      Dafny.ISequence<RAST._IFormal> _out99;
      _out99 = (this).GenParams((m).dtor_params);
      _1335_params = _out99;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1336_paramNames;
      _1336_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1337_paramTypes;
      _1337_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi27 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1338_paramI = BigInteger.Zero; _1338_paramI < _hi27; _1338_paramI++) {
        DAST._IFormal _1339_dafny__formal;
        _1339_dafny__formal = ((m).dtor_params).Select(_1338_paramI);
        RAST._IFormal _1340_formal;
        _1340_formal = (_1335_params).Select(_1338_paramI);
        Dafny.ISequence<Dafny.Rune> _1341_name;
        _1341_name = (_1340_formal).dtor_name;
        _1336_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1336_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1341_name));
        _1337_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1337_paramTypes, _1341_name, (_1340_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1342_fnName;
      _1342_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1343_selfIdent;
      _1343_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1344_selfId;
        _1344_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_1342_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _1344_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv107 = enclosingTypeParams;
        var _pat_let_tv108 = enclosingType;
        DAST._IType _1345_instanceType;
        _1345_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source62 = enclosingType;
          bool unmatched62 = true;
          if (unmatched62) {
            if (_source62.is_UserDefined) {
              DAST._IResolvedType _1346_r = _source62.dtor_resolved;
              unmatched62 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1346_r, _pat_let30_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let30_0, _1347_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv107, _pat_let31_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let31_0, _1348_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1347_dt__update__tmp_h0).dtor_path, _1348_dt__update_htypeArgs_h0, (_1347_dt__update__tmp_h0).dtor_kind, (_1347_dt__update__tmp_h0).dtor_attributes, (_1347_dt__update__tmp_h0).dtor_properMethods, (_1347_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched62) {
            DAST._IType _1349___v59 = _source62;
            unmatched62 = false;
            return _pat_let_tv108;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1350_selfFormal;
          _1350_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1335_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1350_selfFormal), _1335_params);
        } else {
          RAST._IType _1351_tpe;
          RAST._IType _out100;
          _out100 = (this).GenType(_1345_instanceType, DCOMP.GenTypeContext.@default());
          _1351_tpe = _out100;
          if ((_1344_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1351_tpe = RAST.Type.create_Borrowed(_1351_tpe);
          } else if ((_1344_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1351_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1351_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1351_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              _1351_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.Type.create_SelfOwned()));
            }
          }
          _1335_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1344_selfId, _1351_tpe)), _1335_params);
        }
        _1343_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1344_selfId, _1345_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1352_retTypeArgs;
      _1352_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1353_typeI;
      _1353_typeI = BigInteger.Zero;
      while ((_1353_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1354_typeExpr;
        RAST._IType _out101;
        _out101 = (this).GenType(((m).dtor_outTypes).Select(_1353_typeI), DCOMP.GenTypeContext.@default());
        _1354_typeExpr = _out101;
        _1352_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1352_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1354_typeExpr));
        _1353_typeI = (_1353_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1355_visibility;
      _1355_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1356_typeParamsFiltered;
      _1356_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1357_typeParamI = BigInteger.Zero; _1357_typeParamI < _hi28; _1357_typeParamI++) {
        DAST._ITypeArgDecl _1358_typeParam;
        _1358_typeParam = ((m).dtor_typeParams).Select(_1357_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1358_typeParam).dtor_name)))) {
          _1356_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1356_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1358_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1359_typeParams;
      _1359_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1356_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi29 = new BigInteger((_1356_typeParamsFiltered).Count);
        for (BigInteger _1360_i = BigInteger.Zero; _1360_i < _hi29; _1360_i++) {
          DAST._IType _1361_typeArg;
          RAST._ITypeParamDecl _1362_rTypeParamDecl;
          DAST._IType _out102;
          RAST._ITypeParamDecl _out103;
          (this).GenTypeParam((_1356_typeParamsFiltered).Select(_1360_i), out _out102, out _out103);
          _1361_typeArg = _out102;
          _1362_rTypeParamDecl = _out103;
          var _pat_let_tv109 = _1362_rTypeParamDecl;
          _1362_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1362_rTypeParamDecl, _pat_let32_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let32_0, _1363_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv109).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let33_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let33_0, _1364_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1363_dt__update__tmp_h1).dtor_content, _1364_dt__update_hconstraints_h0)))));
          _1359_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1359_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1362_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1365_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1366_env = DCOMP.Environment.Default();
      RAST._IExpr _1367_preBody;
      _1367_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1368_preAssignNames;
      _1368_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1369_preAssignTypes;
      _1369_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        RAST._IExpr _1370_earlyReturn;
        _1370_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source63 = (m).dtor_outVars;
        bool unmatched63 = true;
        if (unmatched63) {
          if (_source63.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1371_outVars = _source63.dtor_value;
            unmatched63 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1370_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(Dafny.Sequence<RAST._IExpr>.FromElements())));
                BigInteger _hi30 = new BigInteger((_1371_outVars).Count);
                for (BigInteger _1372_outI = BigInteger.Zero; _1372_outI < _hi30; _1372_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1373_outVar;
                  _1373_outVar = (_1371_outVars).Select(_1372_outI);
                  Dafny.ISequence<Dafny.Rune> _1374_outName;
                  _1374_outName = DCOMP.__default.escapeName((_1373_outVar));
                  Dafny.ISequence<Dafny.Rune> _1375_tracker__name;
                  _1375_tracker__name = DCOMP.__default.AddAssignedPrefix(_1374_outName);
                  _1368_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1368_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1375_tracker__name));
                  _1369_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1369_preAssignTypes, _1375_tracker__name, RAST.Type.create_Bool());
                  _1367_preBody = (_1367_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1375_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<RAST._IExpr> _1376_tupleArgs;
                _1376_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
                BigInteger _hi31 = new BigInteger((_1371_outVars).Count);
                for (BigInteger _1377_outI = BigInteger.Zero; _1377_outI < _hi31; _1377_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1378_outVar;
                  _1378_outVar = (_1371_outVars).Select(_1377_outI);
                  RAST._IType _1379_outType;
                  RAST._IType _out104;
                  _out104 = (this).GenType(((m).dtor_outTypes).Select(_1377_outI), DCOMP.GenTypeContext.@default());
                  _1379_outType = _out104;
                  Dafny.ISequence<Dafny.Rune> _1380_outName;
                  _1380_outName = DCOMP.__default.escapeName((_1378_outVar));
                  _1336_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1336_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1380_outName));
                  RAST._IType _1381_outMaybeType;
                  _1381_outMaybeType = (((_1379_outType).CanReadWithoutClone()) ? (_1379_outType) : (RAST.__default.MaybePlaceboType(_1379_outType)));
                  _1337_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1337_paramTypes, _1380_outName, _1381_outMaybeType);
                  RAST._IExpr _1382_outVarReturn;
                  DCOMP._IOwnership _1383___v60;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1384___v61;
                  RAST._IExpr _out105;
                  DCOMP._IOwnership _out106;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out107;
                  (this).GenExpr(DAST.Expression.create_Ident((_1378_outVar)), DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1380_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1380_outName, _1381_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out105, out _out106, out _out107);
                  _1382_outVarReturn = _out105;
                  _1383___v60 = _out106;
                  _1384___v61 = _out107;
                  _1376_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1376_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1382_outVarReturn));
                }
                if ((new BigInteger((_1376_tupleArgs).Count)) == (BigInteger.One)) {
                  _1370_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1376_tupleArgs).Select(BigInteger.Zero)));
                } else {
                  _1370_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1376_tupleArgs)));
                }
              }
            }
          }
        }
        if (unmatched63) {
          unmatched63 = false;
        }
        _1366_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1368_preAssignNames, _1336_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1369_preAssignTypes, _1337_paramTypes));
        RAST._IExpr _1385_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1386___v62;
        DCOMP._IEnvironment _1387___v63;
        RAST._IExpr _out108;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out109;
        DCOMP._IEnvironment _out110;
        (this).GenStmts((m).dtor_body, _1343_selfIdent, _1366_env, true, _1370_earlyReturn, out _out108, out _out109, out _out110);
        _1385_body = _out108;
        _1386___v62 = _out109;
        _1387___v63 = _out110;
        _1365_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1367_preBody).Then(_1385_body));
      } else {
        _1366_env = DCOMP.Environment.create(_1336_paramNames, _1337_paramTypes);
        _1365_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1355_visibility, RAST.Fn.create(_1342_fnName, _1359_typeParams, _1335_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1352_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1352_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1352_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1365_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1388_declarations;
      _1388_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1389_i;
      _1389_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1390_stmts;
      _1390_stmts = stmts;
      while ((_1389_i) < (new BigInteger((_1390_stmts).Count))) {
        DAST._IStatement _1391_stmt;
        _1391_stmt = (_1390_stmts).Select(_1389_i);
        DAST._IStatement _source64 = _1391_stmt;
        bool unmatched64 = true;
        if (unmatched64) {
          if (_source64.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1392_name = _source64.dtor_name;
            DAST._IType _1393_optType = _source64.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source64.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched64 = false;
              if (((_1389_i) + (BigInteger.One)) < (new BigInteger((_1390_stmts).Count))) {
                DAST._IStatement _source65 = (_1390_stmts).Select((_1389_i) + (BigInteger.One));
                bool unmatched65 = true;
                if (unmatched65) {
                  if (_source65.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source65.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _1394_name2 = ident0;
                      DAST._IExpression _1395_rhs = _source65.dtor_value;
                      unmatched65 = false;
                      if (object.Equals(_1394_name2, _1392_name)) {
                        _1390_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1390_stmts).Subsequence(BigInteger.Zero, _1389_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1392_name, _1393_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1395_rhs)))), (_1390_stmts).Drop((_1389_i) + (new BigInteger(2))));
                        _1391_stmt = (_1390_stmts).Select(_1389_i);
                      }
                    }
                  }
                }
                if (unmatched65) {
                  DAST._IStatement _1396___v64 = _source65;
                  unmatched65 = false;
                }
              }
            }
          }
        }
        if (unmatched64) {
          DAST._IStatement _1397___v65 = _source64;
          unmatched64 = false;
        }
        RAST._IExpr _1398_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1399_recIdents;
        DCOMP._IEnvironment _1400_newEnv2;
        RAST._IExpr _out111;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out112;
        DCOMP._IEnvironment _out113;
        (this).GenStmt(_1391_stmt, selfIdent, newEnv, (isLast) && ((_1389_i) == ((new BigInteger((_1390_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out111, out _out112, out _out113);
        _1398_stmtExpr = _out111;
        _1399_recIdents = _out112;
        _1400_newEnv2 = _out113;
        newEnv = _1400_newEnv2;
        DAST._IStatement _source66 = _1391_stmt;
        bool unmatched66 = true;
        if (unmatched66) {
          if (_source66.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1401_name = _source66.dtor_name;
            DAST._IType _1402___v66 = _source66.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> _1403___v67 = _source66.dtor_maybeValue;
            unmatched66 = false;
            {
              _1388_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1388_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1401_name)));
            }
          }
        }
        if (unmatched66) {
          DAST._IStatement _1404___v68 = _source66;
          unmatched66 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1399_recIdents, _1388_declarations));
        generated = (generated).Then(_1398_stmtExpr);
        _1389_i = (_1389_i) + (BigInteger.One);
        if ((_1398_stmtExpr).is_Return) {
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
      DAST._IAssignLhs _source67 = lhs;
      bool unmatched67 = true;
      if (unmatched67) {
        if (_source67.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident1 = _source67.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _1405_id = ident1;
          unmatched67 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1406_idRust;
            _1406_idRust = DCOMP.__default.escapeName(_1405_id);
            if (((env).IsBorrowed(_1406_idRust)) || ((env).IsBorrowedMut(_1406_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1406_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1406_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1406_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched67) {
        if (_source67.is_Select) {
          DAST._IExpression _1407_on = _source67.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1408_field = _source67.dtor_field;
          unmatched67 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1409_fieldName;
            _1409_fieldName = DCOMP.__default.escapeName(_1408_field);
            RAST._IExpr _1410_onExpr;
            DCOMP._IOwnership _1411_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1412_recIdents;
            RAST._IExpr _out114;
            DCOMP._IOwnership _out115;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
            (this).GenExpr(_1407_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out114, out _out115, out _out116);
            _1410_onExpr = _out114;
            _1411_onOwned = _out115;
            _1412_recIdents = _out116;
            RAST._IExpr _source68 = _1410_onExpr;
            bool unmatched68 = true;
            if (unmatched68) {
              bool disjunctiveMatch9 = false;
              if (_source68.is_Call) {
                RAST._IExpr obj2 = _source68.dtor_obj;
                if (obj2.is_Select) {
                  RAST._IExpr obj3 = obj2.dtor_obj;
                  if (obj3.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name17 = obj3.dtor_name;
                    if (object.Equals(name17, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      Dafny.ISequence<Dafny.Rune> name18 = obj2.dtor_name;
                      if (object.Equals(name18, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                        Dafny.ISequence<RAST._IExpr> _1413___v69 = _source68.dtor_arguments;
                        disjunctiveMatch9 = true;
                      }
                    }
                  }
                }
              }
              if (_source68.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name19 = _source68.dtor_name;
                if (object.Equals(name19, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch9 = true;
                }
              }
              if (_source68.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op14 = _source68.dtor_op1;
                if (object.Equals(op14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying4 = _source68.dtor_underlying;
                  if (underlying4.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name20 = underlying4.dtor_name;
                    if (object.Equals(name20, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      DAST.Format._IUnaryOpFormat _1414___v70 = _source68.dtor_format;
                      disjunctiveMatch9 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch9) {
                unmatched68 = false;
                Dafny.ISequence<Dafny.Rune> _1415_isAssignedVar;
                _1415_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1409_fieldName);
                if (((newEnv).dtor_names).Contains(_1415_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1409_fieldName), RAST.Expr.create_Identifier(_1415_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1415_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1415_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1409_fieldName, rhs);
                }
              }
            }
            if (unmatched68) {
              RAST._IExpr _1416___v71 = _source68;
              unmatched68 = false;
              if (!object.Equals(_1410_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1410_onExpr = ((this).modify__macro).Apply1(_1410_onExpr);
              }
              generated = RAST.__default.AssignMember(_1410_onExpr, _1409_fieldName, rhs);
            }
            readIdents = _1412_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched67) {
        DAST._IExpression _1417_on = _source67.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1418_indices = _source67.dtor_indices;
        unmatched67 = false;
        {
          RAST._IExpr _1419_onExpr;
          DCOMP._IOwnership _1420_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1421_recIdents;
          RAST._IExpr _out117;
          DCOMP._IOwnership _out118;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out119;
          (this).GenExpr(_1417_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out117, out _out118, out _out119);
          _1419_onExpr = _out117;
          _1420_onOwned = _out118;
          _1421_recIdents = _out119;
          readIdents = _1421_recIdents;
          _1419_onExpr = ((this).modify__macro).Apply1(_1419_onExpr);
          RAST._IExpr _1422_r;
          _1422_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1423_indicesExpr;
          _1423_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_1418_indices).Count);
          for (BigInteger _1424_i = BigInteger.Zero; _1424_i < _hi32; _1424_i++) {
            RAST._IExpr _1425_idx;
            DCOMP._IOwnership _1426___v72;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1427_recIdentsIdx;
            RAST._IExpr _out120;
            DCOMP._IOwnership _out121;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out122;
            (this).GenExpr((_1418_indices).Select(_1424_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out120, out _out121, out _out122);
            _1425_idx = _out120;
            _1426___v72 = _out121;
            _1427_recIdentsIdx = _out122;
            Dafny.ISequence<Dafny.Rune> _1428_varName;
            _1428_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1424_i));
            _1423_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1423_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1428_varName)));
            _1422_r = (_1422_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1428_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), (_1425_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1427_recIdentsIdx);
          }
          if ((new BigInteger((_1418_indices).Count)) > (BigInteger.One)) {
            _1419_onExpr = (_1419_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1429_rhs;
          _1429_rhs = rhs;
          var _pat_let_tv110 = env;
          if (((_1419_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1419_onExpr).LhsIdentifierName(), _pat_let34_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let34_0, _1430_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv110).GetType(_1430_name), _pat_let35_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let35_0, _1431_tpe => ((_1431_tpe).is_Some) && (((_1431_tpe).dtor_value).IsUninitArray())))))))) {
            _1429_rhs = RAST.__default.MaybeUninitNew(_1429_rhs);
          }
          generated = (_1422_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1419_onExpr, _1423_indicesExpr)), _1429_rhs));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source69 = stmt;
      bool unmatched69 = true;
      if (unmatched69) {
        if (_source69.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1432_fields = _source69.dtor_fields;
          unmatched69 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi33 = new BigInteger((_1432_fields).Count);
            for (BigInteger _1433_i = BigInteger.Zero; _1433_i < _hi33; _1433_i++) {
              DAST._IFormal _1434_field;
              _1434_field = (_1432_fields).Select(_1433_i);
              Dafny.ISequence<Dafny.Rune> _1435_fieldName;
              _1435_fieldName = DCOMP.__default.escapeName((_1434_field).dtor_name);
              RAST._IType _1436_fieldTyp;
              RAST._IType _out123;
              _out123 = (this).GenType((_1434_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1436_fieldTyp = _out123;
              Dafny.ISequence<Dafny.Rune> _1437_isAssignedVar;
              _1437_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1435_fieldName);
              if (((newEnv).dtor_names).Contains(_1437_isAssignedVar)) {
                RAST._IExpr _1438_rhs;
                DCOMP._IOwnership _1439___v73;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1440___v74;
                RAST._IExpr _out124;
                DCOMP._IOwnership _out125;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1434_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out124, out _out125, out _out126);
                _1438_rhs = _out124;
                _1439___v73 = _out125;
                _1440___v74 = _out126;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1437_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1435_fieldName), RAST.Expr.create_Identifier(_1437_isAssignedVar), _1438_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1437_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1441_name = _source69.dtor_name;
          DAST._IType _1442_typ = _source69.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source69.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1443_expression = maybeValue1.dtor_value;
            unmatched69 = false;
            {
              RAST._IType _1444_tpe;
              RAST._IType _out127;
              _out127 = (this).GenType(_1442_typ, DCOMP.GenTypeContext.InBinding());
              _1444_tpe = _out127;
              Dafny.ISequence<Dafny.Rune> _1445_varName;
              _1445_varName = DCOMP.__default.escapeName(_1441_name);
              bool _1446_hasCopySemantics;
              _1446_hasCopySemantics = (_1444_tpe).CanReadWithoutClone();
              if (((_1443_expression).is_InitializationValue) && (!(_1446_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1445_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1444_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1445_varName, RAST.__default.MaybePlaceboType(_1444_tpe));
              } else {
                RAST._IExpr _1447_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1448_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1443_expression).is_InitializationValue) && ((_1444_tpe).IsObjectOrPointer())) {
                  _1447_expr = (_1444_tpe).ToNullExpr();
                  _1448_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1449_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out128;
                  DCOMP._IOwnership _out129;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
                  (this).GenExpr(_1443_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out128, out _out129, out _out130);
                  _1447_expr = _out128;
                  _1449_exprOwnership = _out129;
                  _1448_recIdents = _out130;
                }
                readIdents = _1448_recIdents;
                _1444_tpe = (((_1443_expression).is_NewUninitArray) ? ((_1444_tpe).TypeAtInitialization()) : (_1444_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1441_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1444_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1447_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1441_name), _1444_tpe);
              }
            }
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1450_name = _source69.dtor_name;
          DAST._IType _1451_typ = _source69.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source69.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched69 = false;
            {
              DAST._IStatement _1452_newStmt;
              _1452_newStmt = DAST.Statement.create_DeclareVar(_1450_name, _1451_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1451_typ)));
              RAST._IExpr _out131;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out132;
              DCOMP._IEnvironment _out133;
              (this).GenStmt(_1452_newStmt, selfIdent, env, isLast, earlyReturn, out _out131, out _out132, out _out133);
              generated = _out131;
              readIdents = _out132;
              newEnv = _out133;
            }
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Assign) {
          DAST._IAssignLhs _1453_lhs = _source69.dtor_lhs;
          DAST._IExpression _1454_expression = _source69.dtor_value;
          unmatched69 = false;
          {
            RAST._IExpr _1455_exprGen;
            DCOMP._IOwnership _1456___v75;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1457_exprIdents;
            RAST._IExpr _out134;
            DCOMP._IOwnership _out135;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out136;
            (this).GenExpr(_1454_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out134, out _out135, out _out136);
            _1455_exprGen = _out134;
            _1456___v75 = _out135;
            _1457_exprIdents = _out136;
            if ((_1453_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1458_rustId;
              _1458_rustId = DCOMP.__default.escapeName(((_1453_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1459_tpe;
              _1459_tpe = (env).GetType(_1458_rustId);
              if (((_1459_tpe).is_Some) && ((((_1459_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1455_exprGen = RAST.__default.MaybePlacebo(_1455_exprGen);
              }
            }
            RAST._IExpr _1460_lhsGen;
            bool _1461_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1462_recIdents;
            DCOMP._IEnvironment _1463_resEnv;
            RAST._IExpr _out137;
            bool _out138;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out139;
            DCOMP._IEnvironment _out140;
            (this).GenAssignLhs(_1453_lhs, _1455_exprGen, selfIdent, env, out _out137, out _out138, out _out139, out _out140);
            _1460_lhsGen = _out137;
            _1461_needsIIFE = _out138;
            _1462_recIdents = _out139;
            _1463_resEnv = _out140;
            generated = _1460_lhsGen;
            newEnv = _1463_resEnv;
            if (_1461_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1462_recIdents, _1457_exprIdents);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_If) {
          DAST._IExpression _1464_cond = _source69.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1465_thnDafny = _source69.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1466_elsDafny = _source69.dtor_els;
          unmatched69 = false;
          {
            RAST._IExpr _1467_cond;
            DCOMP._IOwnership _1468___v76;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1469_recIdents;
            RAST._IExpr _out141;
            DCOMP._IOwnership _out142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
            (this).GenExpr(_1464_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out141, out _out142, out _out143);
            _1467_cond = _out141;
            _1468___v76 = _out142;
            _1469_recIdents = _out143;
            Dafny.ISequence<Dafny.Rune> _1470_condString;
            _1470_condString = (_1467_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1469_recIdents;
            RAST._IExpr _1471_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1472_thnIdents;
            DCOMP._IEnvironment _1473_thnEnv;
            RAST._IExpr _out144;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out145;
            DCOMP._IEnvironment _out146;
            (this).GenStmts(_1465_thnDafny, selfIdent, env, isLast, earlyReturn, out _out144, out _out145, out _out146);
            _1471_thn = _out144;
            _1472_thnIdents = _out145;
            _1473_thnEnv = _out146;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1472_thnIdents);
            RAST._IExpr _1474_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1475_elsIdents;
            DCOMP._IEnvironment _1476_elsEnv;
            RAST._IExpr _out147;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out148;
            DCOMP._IEnvironment _out149;
            (this).GenStmts(_1466_elsDafny, selfIdent, env, isLast, earlyReturn, out _out147, out _out148, out _out149);
            _1474_els = _out147;
            _1475_elsIdents = _out148;
            _1476_elsEnv = _out149;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1475_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1467_cond, _1471_thn, _1474_els);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1477_lbl = _source69.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1478_body = _source69.dtor_body;
          unmatched69 = false;
          {
            RAST._IExpr _1479_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1480_bodyIdents;
            DCOMP._IEnvironment _1481_env2;
            RAST._IExpr _out150;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out151;
            DCOMP._IEnvironment _out152;
            (this).GenStmts(_1478_body, selfIdent, env, isLast, earlyReturn, out _out150, out _out151, out _out152);
            _1479_body = _out150;
            _1480_bodyIdents = _out151;
            _1481_env2 = _out152;
            readIdents = _1480_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1477_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1479_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_While) {
          DAST._IExpression _1482_cond = _source69.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1483_body = _source69.dtor_body;
          unmatched69 = false;
          {
            RAST._IExpr _1484_cond;
            DCOMP._IOwnership _1485___v77;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1486_recIdents;
            RAST._IExpr _out153;
            DCOMP._IOwnership _out154;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out155;
            (this).GenExpr(_1482_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out153, out _out154, out _out155);
            _1484_cond = _out153;
            _1485___v77 = _out154;
            _1486_recIdents = _out155;
            readIdents = _1486_recIdents;
            RAST._IExpr _1487_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1488_bodyIdents;
            DCOMP._IEnvironment _1489_bodyEnv;
            RAST._IExpr _out156;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out157;
            DCOMP._IEnvironment _out158;
            (this).GenStmts(_1483_body, selfIdent, env, false, earlyReturn, out _out156, out _out157, out _out158);
            _1487_bodyExpr = _out156;
            _1488_bodyIdents = _out157;
            _1489_bodyEnv = _out158;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1488_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1484_cond), _1487_bodyExpr);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1490_boundName = _source69.dtor_boundName;
          DAST._IType _1491_boundType = _source69.dtor_boundType;
          DAST._IExpression _1492_overExpr = _source69.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1493_body = _source69.dtor_body;
          unmatched69 = false;
          {
            RAST._IExpr _1494_over;
            DCOMP._IOwnership _1495___v78;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1496_recIdents;
            RAST._IExpr _out159;
            DCOMP._IOwnership _out160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out161;
            (this).GenExpr(_1492_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out159, out _out160, out _out161);
            _1494_over = _out159;
            _1495___v78 = _out160;
            _1496_recIdents = _out161;
            if (((_1492_overExpr).is_MapBoundedPool) || ((_1492_overExpr).is_SetBoundedPool)) {
              _1494_over = ((_1494_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1497_boundTpe;
            RAST._IType _out162;
            _out162 = (this).GenType(_1491_boundType, DCOMP.GenTypeContext.@default());
            _1497_boundTpe = _out162;
            readIdents = _1496_recIdents;
            Dafny.ISequence<Dafny.Rune> _1498_boundRName;
            _1498_boundRName = DCOMP.__default.escapeName(_1490_boundName);
            RAST._IExpr _1499_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1500_bodyIdents;
            DCOMP._IEnvironment _1501_bodyEnv;
            RAST._IExpr _out163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out164;
            DCOMP._IEnvironment _out165;
            (this).GenStmts(_1493_body, selfIdent, (env).AddAssigned(_1498_boundRName, _1497_boundTpe), false, earlyReturn, out _out163, out _out164, out _out165);
            _1499_bodyExpr = _out163;
            _1500_bodyIdents = _out164;
            _1501_bodyEnv = _out165;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1500_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1498_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1498_boundRName, _1494_over, _1499_bodyExpr);
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1502_toLabel = _source69.dtor_toLabel;
          unmatched69 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source70 = _1502_toLabel;
            bool unmatched70 = true;
            if (unmatched70) {
              if (_source70.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1503_lbl = _source70.dtor_value;
                unmatched70 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1503_lbl)));
                }
              }
            }
            if (unmatched70) {
              unmatched70 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1504_body = _source69.dtor_body;
          unmatched69 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1505_selfClone;
              DCOMP._IOwnership _1506___v79;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1507___v80;
              RAST._IExpr _out166;
              DCOMP._IOwnership _out167;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out168;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out166, out _out167, out _out168);
              _1505_selfClone = _out166;
              _1506___v79 = _out167;
              _1507___v80 = _out168;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1505_selfClone)));
            }
            newEnv = env;
            BigInteger _hi34 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1508_paramI = BigInteger.Zero; _1508_paramI < _hi34; _1508_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1509_param;
              _1509_param = ((env).dtor_names).Select(_1508_paramI);
              RAST._IExpr _1510_paramInit;
              DCOMP._IOwnership _1511___v81;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1512___v82;
              RAST._IExpr _out169;
              DCOMP._IOwnership _out170;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out171;
              (this).GenIdent(_1509_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out169, out _out170, out _out171);
              _1510_paramInit = _out169;
              _1511___v81 = _out170;
              _1512___v82 = _out171;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1509_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1510_paramInit)));
              if (((env).dtor_types).Contains(_1509_param)) {
                RAST._IType _1513_declaredType;
                _1513_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1509_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1509_param, _1513_declaredType);
              }
            }
            RAST._IExpr _1514_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1515_bodyIdents;
            DCOMP._IEnvironment _1516_bodyEnv;
            RAST._IExpr _out172;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out173;
            DCOMP._IEnvironment _out174;
            (this).GenStmts(_1504_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out172, out _out173, out _out174);
            _1514_bodyExpr = _out172;
            _1515_bodyIdents = _out173;
            _1516_bodyEnv = _out174;
            readIdents = _1515_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1514_bodyExpr)));
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_JumpTailCallStart) {
          unmatched69 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Call) {
          DAST._IExpression _1517_on = _source69.dtor_on;
          DAST._ICallName _1518_name = _source69.dtor_callName;
          Dafny.ISequence<DAST._IType> _1519_typeArgs = _source69.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1520_args = _source69.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1521_maybeOutVars = _source69.dtor_outs;
          unmatched69 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1522_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1523_recIdents;
            Dafny.ISequence<RAST._IType> _1524_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1525_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out175;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out176;
            Dafny.ISequence<RAST._IType> _out177;
            Std.Wrappers._IOption<DAST._IResolvedType> _out178;
            (this).GenArgs(selfIdent, _1518_name, _1519_typeArgs, _1520_args, env, out _out175, out _out176, out _out177, out _out178);
            _1522_argExprs = _out175;
            _1523_recIdents = _out176;
            _1524_typeExprs = _out177;
            _1525_fullNameQualifier = _out178;
            readIdents = _1523_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source71 = _1525_fullNameQualifier;
            bool unmatched71 = true;
            if (unmatched71) {
              if (_source71.is_Some) {
                DAST._IResolvedType value9 = _source71.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1526_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1527_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1528_base = value9.dtor_kind;
                Dafny.ISequence<DAST._IAttribute> _1529___v83 = value9.dtor_attributes;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1530___v84 = value9.dtor_properMethods;
                Dafny.ISequence<DAST._IType> _1531___v85 = value9.dtor_extendedTypes;
                unmatched71 = false;
                RAST._IExpr _1532_fullPath;
                RAST._IExpr _out179;
                _out179 = DCOMP.COMP.GenPathExpr(_1526_path);
                _1532_fullPath = _out179;
                Dafny.ISequence<RAST._IType> _1533_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out180;
                _out180 = (this).GenTypeArgs(_1527_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1533_onTypeExprs = _out180;
                RAST._IExpr _1534_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1535_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1536_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1528_base).is_Trait) || ((_1528_base).is_Class)) {
                  RAST._IExpr _out181;
                  DCOMP._IOwnership _out182;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out183;
                  (this).GenExpr(_1517_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out181, out _out182, out _out183);
                  _1534_onExpr = _out181;
                  _1535_recOwnership = _out182;
                  _1536_recIdents = _out183;
                  _1534_onExpr = ((this).modify__macro).Apply1(_1534_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1536_recIdents);
                } else {
                  RAST._IExpr _out184;
                  DCOMP._IOwnership _out185;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out186;
                  (this).GenExpr(_1517_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out184, out _out185, out _out186);
                  _1534_onExpr = _out184;
                  _1535_recOwnership = _out185;
                  _1536_recIdents = _out186;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1536_recIdents);
                }
                generated = ((((_1532_fullPath).ApplyType(_1533_onTypeExprs)).MSel(DCOMP.__default.escapeName((_1518_name).dtor_name))).ApplyType(_1524_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1534_onExpr), _1522_argExprs));
              }
            }
            if (unmatched71) {
              Std.Wrappers._IOption<DAST._IResolvedType> _1537___v86 = _source71;
              unmatched71 = false;
              RAST._IExpr _1538_onExpr;
              DCOMP._IOwnership _1539___v87;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1540_enclosingIdents;
              RAST._IExpr _out187;
              DCOMP._IOwnership _out188;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out189;
              (this).GenExpr(_1517_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out187, out _out188, out _out189);
              _1538_onExpr = _out187;
              _1539___v87 = _out188;
              _1540_enclosingIdents = _out189;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1540_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1541_renderedName;
              _1541_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
                DAST._ICallName _source72 = _1518_name;
                bool unmatched72 = true;
                if (unmatched72) {
                  if (_source72.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _1542_name = _source72.dtor_name;
                    Std.Wrappers._IOption<DAST._IType> _1543___v88 = _source72.dtor_onType;
                    Std.Wrappers._IOption<DAST._IFormal> _1544___v89 = _source72.dtor_receiverArgs;
                    Dafny.ISequence<DAST._IFormal> _1545___v90 = _source72.dtor_signature;
                    unmatched72 = false;
                    return DCOMP.__default.escapeName(_1542_name);
                  }
                }
                if (unmatched72) {
                  bool disjunctiveMatch10 = false;
                  if (_source72.is_MapBuilderAdd) {
                    disjunctiveMatch10 = true;
                  }
                  if (_source72.is_SetBuilderAdd) {
                    disjunctiveMatch10 = true;
                  }
                  if (disjunctiveMatch10) {
                    unmatched72 = false;
                    return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  }
                }
                if (unmatched72) {
                  bool disjunctiveMatch11 = false;
                  disjunctiveMatch11 = true;
                  disjunctiveMatch11 = true;
                  if (disjunctiveMatch11) {
                    unmatched72 = false;
                    return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                  }
                }
                throw new System.Exception("unexpected control point");
              }))();
              DAST._IExpression _source73 = _1517_on;
              bool unmatched73 = true;
              if (unmatched73) {
                if (_source73.is_Companion) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1546___v91 = _source73.dtor_Companion_a0;
                  Dafny.ISequence<DAST._IType> _1547___v92 = _source73.dtor_typeArgs;
                  unmatched73 = false;
                  {
                    _1538_onExpr = (_1538_onExpr).MSel(_1541_renderedName);
                  }
                }
              }
              if (unmatched73) {
                DAST._IExpression _1548___v93 = _source73;
                unmatched73 = false;
                {
                  if (!object.Equals(_1538_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source74 = _1518_name;
                    bool unmatched74 = true;
                    if (unmatched74) {
                      if (_source74.is_CallName) {
                        Dafny.ISequence<Dafny.Rune> _1549___v94 = _source74.dtor_name;
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source74.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1550_tpe = onType0.dtor_value;
                          Std.Wrappers._IOption<DAST._IFormal> _1551___v95 = _source74.dtor_receiverArgs;
                          Dafny.ISequence<DAST._IFormal> _1552___v96 = _source74.dtor_signature;
                          unmatched74 = false;
                          RAST._IType _1553_typ;
                          RAST._IType _out190;
                          _out190 = (this).GenType(_1550_tpe, DCOMP.GenTypeContext.@default());
                          _1553_typ = _out190;
                          if (((_1553_typ).IsObjectOrPointer()) && (!object.Equals(_1538_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1538_onExpr = ((this).modify__macro).Apply1(_1538_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched74) {
                      DAST._ICallName _1554___v97 = _source74;
                      unmatched74 = false;
                    }
                  }
                  _1538_onExpr = (_1538_onExpr).Sel(_1541_renderedName);
                }
              }
              generated = ((_1538_onExpr).ApplyType(_1524_typeExprs)).Apply(_1522_argExprs);
            }
            if (((_1521_maybeOutVars).is_Some) && ((new BigInteger(((_1521_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1555_outVar;
              _1555_outVar = DCOMP.__default.escapeName((((_1521_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1555_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1555_outVar, generated);
            } else if (((_1521_maybeOutVars).is_None) || ((new BigInteger(((_1521_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1556_tmpVar;
              _1556_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1557_tmpId;
              _1557_tmpId = RAST.Expr.create_Identifier(_1556_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1556_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1558_outVars;
              _1558_outVars = (_1521_maybeOutVars).dtor_value;
              BigInteger _hi35 = new BigInteger((_1558_outVars).Count);
              for (BigInteger _1559_outI = BigInteger.Zero; _1559_outI < _hi35; _1559_outI++) {
                Dafny.ISequence<Dafny.Rune> _1560_outVar;
                _1560_outVar = DCOMP.__default.escapeName(((_1558_outVars).Select(_1559_outI)));
                RAST._IExpr _1561_rhs;
                _1561_rhs = (_1557_tmpId).Sel(Std.Strings.__default.OfNat(_1559_outI));
                if (!((env).CanReadWithoutClone(_1560_outVar))) {
                  _1561_rhs = RAST.__default.MaybePlacebo(_1561_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1560_outVar, _1561_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Return) {
          DAST._IExpression _1562_exprDafny = _source69.dtor_expr;
          unmatched69 = false;
          {
            RAST._IExpr _1563_expr;
            DCOMP._IOwnership _1564___v98;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1565_recIdents;
            RAST._IExpr _out191;
            DCOMP._IOwnership _out192;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
            (this).GenExpr(_1562_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out191, out _out192, out _out193);
            _1563_expr = _out191;
            _1564___v98 = _out192;
            _1565_recIdents = _out193;
            readIdents = _1565_recIdents;
            if (isLast) {
              generated = _1563_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1563_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_EarlyReturn) {
          unmatched69 = false;
          {
            generated = earlyReturn;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched69) {
        if (_source69.is_Halt) {
          unmatched69 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched69) {
        DAST._IExpression _1566_e = _source69.dtor_Print_a0;
        unmatched69 = false;
        {
          RAST._IExpr _1567_printedExpr;
          DCOMP._IOwnership _1568_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1569_recIdents;
          RAST._IExpr _out194;
          DCOMP._IOwnership _out195;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out196;
          (this).GenExpr(_1566_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out194, out _out195, out _out196);
          _1567_printedExpr = _out194;
          _1568_recOwnership = _out195;
          _1569_recIdents = _out196;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1567_printedExpr)));
          readIdents = _1569_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source75 = range;
      bool unmatched75 = true;
      if (unmatched75) {
        if (_source75.is_NoRange) {
          unmatched75 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched75) {
        if (_source75.is_U8) {
          unmatched75 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched75) {
        if (_source75.is_U16) {
          unmatched75 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched75) {
        if (_source75.is_U32) {
          unmatched75 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched75) {
        if (_source75.is_U64) {
          unmatched75 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched75) {
        if (_source75.is_U128) {
          unmatched75 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched75) {
        if (_source75.is_I8) {
          unmatched75 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched75) {
        if (_source75.is_I16) {
          unmatched75 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched75) {
        if (_source75.is_I32) {
          unmatched75 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched75) {
        if (_source75.is_I64) {
          unmatched75 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched75) {
        if (_source75.is_I128) {
          unmatched75 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched75) {
        DAST._INewtypeRange _1570___v99 = _source75;
        unmatched75 = false;
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
      DAST._IExpression _source76 = e;
      bool unmatched76 = true;
      if (unmatched76) {
        if (_source76.is_Literal) {
          DAST._ILiteral _h130 = _source76.dtor_Literal_a0;
          if (_h130.is_BoolLiteral) {
            bool _1571_b = _h130.dtor_BoolLiteral_a0;
            unmatched76 = false;
            {
              RAST._IExpr _out201;
              DCOMP._IOwnership _out202;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1571_b), expectedOwnership, out _out201, out _out202);
              r = _out201;
              resultingOwnership = _out202;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched76) {
        if (_source76.is_Literal) {
          DAST._ILiteral _h131 = _source76.dtor_Literal_a0;
          if (_h131.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1572_i = _h131.dtor_IntLiteral_a0;
            DAST._IType _1573_t = _h131.dtor_IntLiteral_a1;
            unmatched76 = false;
            {
              DAST._IType _source77 = _1573_t;
              bool unmatched77 = true;
              if (unmatched77) {
                if (_source77.is_Primitive) {
                  DAST._IPrimitive _h70 = _source77.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched77 = false;
                    {
                      if ((new BigInteger((_1572_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1572_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1572_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched77) {
                DAST._IType _1574_o = _source77;
                unmatched77 = false;
                {
                  RAST._IType _1575_genType;
                  RAST._IType _out203;
                  _out203 = (this).GenType(_1574_o, DCOMP.GenTypeContext.@default());
                  _1575_genType = _out203;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1572_i), _1575_genType);
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
      if (unmatched76) {
        if (_source76.is_Literal) {
          DAST._ILiteral _h132 = _source76.dtor_Literal_a0;
          if (_h132.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1576_n = _h132.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1577_d = _h132.dtor_DecLiteral_a1;
            DAST._IType _1578_t = _h132.dtor_DecLiteral_a2;
            unmatched76 = false;
            {
              DAST._IType _source78 = _1578_t;
              bool unmatched78 = true;
              if (unmatched78) {
                if (_source78.is_Primitive) {
                  DAST._IPrimitive _h71 = _source78.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched78 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1576_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1577_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched78) {
                DAST._IType _1579_o = _source78;
                unmatched78 = false;
                {
                  RAST._IType _1580_genType;
                  RAST._IType _out206;
                  _out206 = (this).GenType(_1579_o, DCOMP.GenTypeContext.@default());
                  _1580_genType = _out206;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1576_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1577_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1580_genType);
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
      if (unmatched76) {
        if (_source76.is_Literal) {
          DAST._ILiteral _h133 = _source76.dtor_Literal_a0;
          if (_h133.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1581_l = _h133.dtor_StringLiteral_a0;
            bool _1582_verbatim = _h133.dtor_verbatim;
            unmatched76 = false;
            {
              if (_1582_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1581_l, false, _1582_verbatim));
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
      if (unmatched76) {
        if (_source76.is_Literal) {
          DAST._ILiteral _h134 = _source76.dtor_Literal_a0;
          if (_h134.is_CharLiteralUTF16) {
            BigInteger _1583_c = _h134.dtor_CharLiteralUTF16_a0;
            unmatched76 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1583_c));
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
      if (unmatched76) {
        if (_source76.is_Literal) {
          DAST._ILiteral _h135 = _source76.dtor_Literal_a0;
          if (_h135.is_CharLiteral) {
            Dafny.Rune _1584_c = _h135.dtor_CharLiteral_a0;
            unmatched76 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1584_c).Value)));
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
      if (unmatched76) {
        DAST._ILiteral _h136 = _source76.dtor_Literal_a0;
        DAST._IType _1585_tpe = _h136.dtor_Null_a0;
        unmatched76 = false;
        {
          RAST._IType _1586_tpeGen;
          RAST._IType _out215;
          _out215 = (this).GenType(_1585_tpe, DCOMP.GenTypeContext.@default());
          _1586_tpeGen = _out215;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"));
          } else {
            r = RAST.Expr.create_TypeAscription(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1586_tpeGen);
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
      DAST._IBinOp _1587_op = _let_tmp_rhs53.dtor_op;
      DAST._IExpression _1588_lExpr = _let_tmp_rhs53.dtor_left;
      DAST._IExpression _1589_rExpr = _let_tmp_rhs53.dtor_right;
      DAST.Format._IBinaryOpFormat _1590_format = _let_tmp_rhs53.dtor_format2;
      bool _1591_becomesLeftCallsRight;
      _1591_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source79 = _1587_op;
        bool unmatched79 = true;
        if (unmatched79) {
          bool disjunctiveMatch12 = false;
          if (_source79.is_SetMerge) {
            disjunctiveMatch12 = true;
          }
          if (_source79.is_SetSubtraction) {
            disjunctiveMatch12 = true;
          }
          if (_source79.is_SetIntersection) {
            disjunctiveMatch12 = true;
          }
          if (_source79.is_SetDisjoint) {
            disjunctiveMatch12 = true;
          }
          if (_source79.is_MapMerge) {
            disjunctiveMatch12 = true;
          }
          if (_source79.is_MapSubtraction) {
            disjunctiveMatch12 = true;
          }
          if (_source79.is_MultisetMerge) {
            disjunctiveMatch12 = true;
          }
          if (_source79.is_MultisetSubtraction) {
            disjunctiveMatch12 = true;
          }
          if (_source79.is_MultisetIntersection) {
            disjunctiveMatch12 = true;
          }
          if (_source79.is_MultisetDisjoint) {
            disjunctiveMatch12 = true;
          }
          if (_source79.is_Concat) {
            disjunctiveMatch12 = true;
          }
          if (disjunctiveMatch12) {
            unmatched79 = false;
            return true;
          }
        }
        if (unmatched79) {
          DAST._IBinOp _1592___v100 = _source79;
          unmatched79 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1593_becomesRightCallsLeft;
      _1593_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source80 = _1587_op;
        bool unmatched80 = true;
        if (unmatched80) {
          if (_source80.is_In) {
            unmatched80 = false;
            return true;
          }
        }
        if (unmatched80) {
          DAST._IBinOp _1594___v101 = _source80;
          unmatched80 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1595_becomesCallLeftRight;
      _1595_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source81 = _1587_op;
        bool unmatched81 = true;
        if (unmatched81) {
          if (_source81.is_Eq) {
            bool referential0 = _source81.dtor_referential;
            if ((referential0) == (true)) {
              unmatched81 = false;
              return false;
            }
          }
        }
        if (unmatched81) {
          if (_source81.is_SetMerge) {
            unmatched81 = false;
            return true;
          }
        }
        if (unmatched81) {
          if (_source81.is_SetSubtraction) {
            unmatched81 = false;
            return true;
          }
        }
        if (unmatched81) {
          if (_source81.is_SetIntersection) {
            unmatched81 = false;
            return true;
          }
        }
        if (unmatched81) {
          if (_source81.is_SetDisjoint) {
            unmatched81 = false;
            return true;
          }
        }
        if (unmatched81) {
          if (_source81.is_MapMerge) {
            unmatched81 = false;
            return true;
          }
        }
        if (unmatched81) {
          if (_source81.is_MapSubtraction) {
            unmatched81 = false;
            return true;
          }
        }
        if (unmatched81) {
          if (_source81.is_MultisetMerge) {
            unmatched81 = false;
            return true;
          }
        }
        if (unmatched81) {
          if (_source81.is_MultisetSubtraction) {
            unmatched81 = false;
            return true;
          }
        }
        if (unmatched81) {
          if (_source81.is_MultisetIntersection) {
            unmatched81 = false;
            return true;
          }
        }
        if (unmatched81) {
          if (_source81.is_MultisetDisjoint) {
            unmatched81 = false;
            return true;
          }
        }
        if (unmatched81) {
          if (_source81.is_Concat) {
            unmatched81 = false;
            return true;
          }
        }
        if (unmatched81) {
          DAST._IBinOp _1596___v102 = _source81;
          unmatched81 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1597_expectedLeftOwnership;
      _1597_expectedLeftOwnership = ((_1591_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1593_becomesRightCallsLeft) || (_1595_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1598_expectedRightOwnership;
      _1598_expectedRightOwnership = (((_1591_becomesLeftCallsRight) || (_1595_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1593_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1599_left;
      DCOMP._IOwnership _1600___v103;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1601_recIdentsL;
      RAST._IExpr _out218;
      DCOMP._IOwnership _out219;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out220;
      (this).GenExpr(_1588_lExpr, selfIdent, env, _1597_expectedLeftOwnership, out _out218, out _out219, out _out220);
      _1599_left = _out218;
      _1600___v103 = _out219;
      _1601_recIdentsL = _out220;
      RAST._IExpr _1602_right;
      DCOMP._IOwnership _1603___v104;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1604_recIdentsR;
      RAST._IExpr _out221;
      DCOMP._IOwnership _out222;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out223;
      (this).GenExpr(_1589_rExpr, selfIdent, env, _1598_expectedRightOwnership, out _out221, out _out222, out _out223);
      _1602_right = _out221;
      _1603___v104 = _out222;
      _1604_recIdentsR = _out223;
      DAST._IBinOp _source82 = _1587_op;
      bool unmatched82 = true;
      if (unmatched82) {
        if (_source82.is_In) {
          unmatched82 = false;
          {
            r = ((_1602_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1599_left);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_SeqProperPrefix) {
          unmatched82 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1599_left, _1602_right, _1590_format);
        }
      }
      if (unmatched82) {
        if (_source82.is_SeqPrefix) {
          unmatched82 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1599_left, _1602_right, _1590_format);
        }
      }
      if (unmatched82) {
        if (_source82.is_SetMerge) {
          unmatched82 = false;
          {
            r = ((_1599_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1602_right);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_SetSubtraction) {
          unmatched82 = false;
          {
            r = ((_1599_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1602_right);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_SetIntersection) {
          unmatched82 = false;
          {
            r = ((_1599_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1602_right);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_Subset) {
          unmatched82 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1599_left, _1602_right, _1590_format);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_ProperSubset) {
          unmatched82 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1599_left, _1602_right, _1590_format);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_SetDisjoint) {
          unmatched82 = false;
          {
            r = ((_1599_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1602_right);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_MapMerge) {
          unmatched82 = false;
          {
            r = ((_1599_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1602_right);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_MapSubtraction) {
          unmatched82 = false;
          {
            r = ((_1599_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1602_right);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_MultisetMerge) {
          unmatched82 = false;
          {
            r = ((_1599_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1602_right);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_MultisetSubtraction) {
          unmatched82 = false;
          {
            r = ((_1599_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1602_right);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_MultisetIntersection) {
          unmatched82 = false;
          {
            r = ((_1599_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1602_right);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_Submultiset) {
          unmatched82 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1599_left, _1602_right, _1590_format);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_ProperSubmultiset) {
          unmatched82 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1599_left, _1602_right, _1590_format);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_MultisetDisjoint) {
          unmatched82 = false;
          {
            r = ((_1599_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1602_right);
          }
        }
      }
      if (unmatched82) {
        if (_source82.is_Concat) {
          unmatched82 = false;
          {
            r = ((_1599_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1602_right);
          }
        }
      }
      if (unmatched82) {
        DAST._IBinOp _1605___v105 = _source82;
        unmatched82 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1587_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1587_op), _1599_left, _1602_right, _1590_format);
          } else {
            DAST._IBinOp _source83 = _1587_op;
            bool unmatched83 = true;
            if (unmatched83) {
              if (_source83.is_Eq) {
                bool _1606_referential = _source83.dtor_referential;
                unmatched83 = false;
                {
                  if (_1606_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1599_left, _1602_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1589_rExpr).is_SeqValue) && ((new BigInteger(((_1589_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1599_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1588_lExpr).is_SeqValue) && ((new BigInteger(((_1588_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1602_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1599_left, _1602_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched83) {
              if (_source83.is_EuclidianDiv) {
                unmatched83 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1599_left, _1602_right));
                }
              }
            }
            if (unmatched83) {
              if (_source83.is_EuclidianMod) {
                unmatched83 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1599_left, _1602_right));
                }
              }
            }
            if (unmatched83) {
              Dafny.ISequence<Dafny.Rune> _1607_op = _source83.dtor_Passthrough_a0;
              unmatched83 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1607_op, _1599_left, _1602_right, _1590_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1601_recIdentsL, _1604_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _1608_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _1609_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _1610_toTpe = _let_tmp_rhs54.dtor_typ;
      DAST._IType _let_tmp_rhs55 = _1610_toTpe;
      DAST._IResolvedType _let_tmp_rhs56 = _let_tmp_rhs55.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1611_path = _let_tmp_rhs56.dtor_path;
      Dafny.ISequence<DAST._IType> _1612_typeArgs = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs57 = _let_tmp_rhs56.dtor_kind;
      DAST._IType _1613_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1614_range = _let_tmp_rhs57.dtor_range;
      bool _1615_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1616___v106 = _let_tmp_rhs56.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1617___v107 = _let_tmp_rhs56.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1618___v108 = _let_tmp_rhs56.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1619_nativeToType;
      _1619_nativeToType = DCOMP.COMP.NewtypeToRustType(_1613_b, _1614_range);
      if (object.Equals(_1609_fromTpe, _1613_b)) {
        RAST._IExpr _1620_recursiveGen;
        DCOMP._IOwnership _1621_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1622_recIdents;
        RAST._IExpr _out226;
        DCOMP._IOwnership _out227;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out228;
        (this).GenExpr(_1608_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out226, out _out227, out _out228);
        _1620_recursiveGen = _out226;
        _1621_recOwned = _out227;
        _1622_recIdents = _out228;
        readIdents = _1622_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source84 = _1619_nativeToType;
        bool unmatched84 = true;
        if (unmatched84) {
          if (_source84.is_Some) {
            RAST._IType _1623_v = _source84.dtor_value;
            unmatched84 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1620_recursiveGen, RAST.Expr.create_ExprFromType(_1623_v)));
            RAST._IExpr _out229;
            DCOMP._IOwnership _out230;
            (this).FromOwned(r, expectedOwnership, out _out229, out _out230);
            r = _out229;
            resultingOwnership = _out230;
          }
        }
        if (unmatched84) {
          unmatched84 = false;
          if (_1615_erase) {
            r = _1620_recursiveGen;
          } else {
            RAST._IType _1624_rhsType;
            RAST._IType _out231;
            _out231 = (this).GenType(_1610_toTpe, DCOMP.GenTypeContext.InBinding());
            _1624_rhsType = _out231;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1624_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1620_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out232;
          DCOMP._IOwnership _out233;
          (this).FromOwnership(r, _1621_recOwned, expectedOwnership, out _out232, out _out233);
          r = _out232;
          resultingOwnership = _out233;
        }
      } else {
        if ((_1619_nativeToType).is_Some) {
          DAST._IType _source85 = _1609_fromTpe;
          bool unmatched85 = true;
          if (unmatched85) {
            if (_source85.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source85.dtor_resolved;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1625___v109 = resolved1.dtor_path;
              Dafny.ISequence<DAST._IType> _1626___v110 = resolved1.dtor_typeArgs;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1627_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1628_range0 = kind1.dtor_range;
                bool _1629_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1630_attributes0 = resolved1.dtor_attributes;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1631___v111 = resolved1.dtor_properMethods;
                Dafny.ISequence<DAST._IType> _1632___v112 = resolved1.dtor_extendedTypes;
                unmatched85 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1633_nativeFromType;
                  _1633_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1627_b0, _1628_range0);
                  if ((_1633_nativeFromType).is_Some) {
                    RAST._IExpr _1634_recursiveGen;
                    DCOMP._IOwnership _1635_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1636_recIdents;
                    RAST._IExpr _out234;
                    DCOMP._IOwnership _out235;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out236;
                    (this).GenExpr(_1608_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out234, out _out235, out _out236);
                    _1634_recursiveGen = _out234;
                    _1635_recOwned = _out235;
                    _1636_recIdents = _out236;
                    RAST._IExpr _out237;
                    DCOMP._IOwnership _out238;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1634_recursiveGen, (_1619_nativeToType).dtor_value), _1635_recOwned, expectedOwnership, out _out237, out _out238);
                    r = _out237;
                    resultingOwnership = _out238;
                    readIdents = _1636_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched85) {
            DAST._IType _1637___v113 = _source85;
            unmatched85 = false;
          }
          if (object.Equals(_1609_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1638_recursiveGen;
            DCOMP._IOwnership _1639_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1640_recIdents;
            RAST._IExpr _out239;
            DCOMP._IOwnership _out240;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out241;
            (this).GenExpr(_1608_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out239, out _out240, out _out241);
            _1638_recursiveGen = _out239;
            _1639_recOwned = _out240;
            _1640_recIdents = _out241;
            RAST._IExpr _out242;
            DCOMP._IOwnership _out243;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1638_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1619_nativeToType).dtor_value), _1639_recOwned, expectedOwnership, out _out242, out _out243);
            r = _out242;
            resultingOwnership = _out243;
            readIdents = _1640_recIdents;
            return ;
          }
        }
        RAST._IExpr _out244;
        DCOMP._IOwnership _out245;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out246;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1608_expr, _1609_fromTpe, _1613_b), _1613_b, _1610_toTpe), selfIdent, env, expectedOwnership, out _out244, out _out245, out _out246);
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
      DAST._IExpression _1641_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1642_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1643_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _1642_fromTpe;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1644___v114 = _let_tmp_rhs60.dtor_path;
      Dafny.ISequence<DAST._IType> _1645___v115 = _let_tmp_rhs60.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs61 = _let_tmp_rhs60.dtor_kind;
      DAST._IType _1646_b = _let_tmp_rhs61.dtor_baseType;
      DAST._INewtypeRange _1647_range = _let_tmp_rhs61.dtor_range;
      bool _1648_erase = _let_tmp_rhs61.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1649_attributes = _let_tmp_rhs60.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1650___v116 = _let_tmp_rhs60.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1651___v117 = _let_tmp_rhs60.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1652_nativeFromType;
      _1652_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1646_b, _1647_range);
      if (object.Equals(_1646_b, _1643_toTpe)) {
        RAST._IExpr _1653_recursiveGen;
        DCOMP._IOwnership _1654_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1655_recIdents;
        RAST._IExpr _out247;
        DCOMP._IOwnership _out248;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out249;
        (this).GenExpr(_1641_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out247, out _out248, out _out249);
        _1653_recursiveGen = _out247;
        _1654_recOwned = _out248;
        _1655_recIdents = _out249;
        readIdents = _1655_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source86 = _1652_nativeFromType;
        bool unmatched86 = true;
        if (unmatched86) {
          if (_source86.is_Some) {
            RAST._IType _1656_v = _source86.dtor_value;
            unmatched86 = false;
            RAST._IType _1657_toTpeRust;
            RAST._IType _out250;
            _out250 = (this).GenType(_1643_toTpe, DCOMP.GenTypeContext.@default());
            _1657_toTpeRust = _out250;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1657_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1653_recursiveGen));
            RAST._IExpr _out251;
            DCOMP._IOwnership _out252;
            (this).FromOwned(r, expectedOwnership, out _out251, out _out252);
            r = _out251;
            resultingOwnership = _out252;
          }
        }
        if (unmatched86) {
          unmatched86 = false;
          if (_1648_erase) {
            r = _1653_recursiveGen;
          } else {
            r = (_1653_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out253;
          DCOMP._IOwnership _out254;
          (this).FromOwnership(r, _1654_recOwned, expectedOwnership, out _out253, out _out254);
          r = _out253;
          resultingOwnership = _out254;
        }
      } else {
        if ((_1652_nativeFromType).is_Some) {
          if (object.Equals(_1643_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1658_recursiveGen;
            DCOMP._IOwnership _1659_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1660_recIdents;
            RAST._IExpr _out255;
            DCOMP._IOwnership _out256;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out257;
            (this).GenExpr(_1641_expr, selfIdent, env, expectedOwnership, out _out255, out _out256, out _out257);
            _1658_recursiveGen = _out255;
            _1659_recOwned = _out256;
            _1660_recIdents = _out257;
            RAST._IExpr _out258;
            DCOMP._IOwnership _out259;
            (this).FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1658_recursiveGen, (this).DafnyCharUnderlying)), _1659_recOwned, expectedOwnership, out _out258, out _out259);
            r = _out258;
            resultingOwnership = _out259;
            readIdents = _1660_recIdents;
            return ;
          }
        }
        RAST._IExpr _out260;
        DCOMP._IOwnership _out261;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out262;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1641_expr, _1642_fromTpe, _1646_b), _1646_b, _1643_toTpe), selfIdent, env, expectedOwnership, out _out260, out _out261, out _out262);
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
      DAST._IExpression _1661_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _1662_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _1663_toTpe = _let_tmp_rhs62.dtor_typ;
      RAST._IType _1664_fromTpeGen;
      RAST._IType _out263;
      _out263 = (this).GenType(_1662_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1664_fromTpeGen = _out263;
      RAST._IType _1665_toTpeGen;
      RAST._IType _out264;
      _out264 = (this).GenType(_1663_toTpe, DCOMP.GenTypeContext.InBinding());
      _1665_toTpeGen = _out264;
      if (RAST.__default.IsUpcastConversion(_1664_fromTpeGen, _1665_toTpeGen)) {
        RAST._IExpr _1666_recursiveGen;
        DCOMP._IOwnership _1667_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1668_recIdents;
        RAST._IExpr _out265;
        DCOMP._IOwnership _out266;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out267;
        (this).GenExpr(_1661_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out265, out _out266, out _out267);
        _1666_recursiveGen = _out265;
        _1667_recOwned = _out266;
        _1668_recIdents = _out267;
        readIdents = _1668_recIdents;
        if ((_1665_toTpeGen).IsObjectOrPointer()) {
          _1665_toTpeGen = (_1665_toTpeGen).ObjectOrPointerUnderlying();
        }
        r = ((((RAST.__default.dafny__runtime).MSel((this).upcast)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_")), _1665_toTpeGen))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Apply1(_1666_recursiveGen);
        RAST._IExpr _out268;
        DCOMP._IOwnership _out269;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out268, out _out269);
        r = _out268;
        resultingOwnership = _out269;
      } else {
        RAST._IExpr _1669_recursiveGen;
        DCOMP._IOwnership _1670_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1671_recIdents;
        RAST._IExpr _out270;
        DCOMP._IOwnership _out271;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out272;
        (this).GenExpr(_1661_expr, selfIdent, env, expectedOwnership, out _out270, out _out271, out _out272);
        _1669_recursiveGen = _out270;
        _1670_recOwned = _out271;
        _1671_recIdents = _out272;
        readIdents = _1671_recIdents;
        Dafny.ISequence<Dafny.Rune> _1672_msg;
        _1672_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1664_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1665_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1672_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1669_recursiveGen)._ToString(DCOMP.__default.IND), _1672_msg));
        RAST._IExpr _out273;
        DCOMP._IOwnership _out274;
        (this).FromOwnership(r, _1670_recOwned, expectedOwnership, out _out273, out _out274);
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
      DAST._IExpression _1673_expr = _let_tmp_rhs63.dtor_value;
      DAST._IType _1674_fromTpe = _let_tmp_rhs63.dtor_from;
      DAST._IType _1675_toTpe = _let_tmp_rhs63.dtor_typ;
      if (object.Equals(_1674_fromTpe, _1675_toTpe)) {
        RAST._IExpr _1676_recursiveGen;
        DCOMP._IOwnership _1677_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1678_recIdents;
        RAST._IExpr _out275;
        DCOMP._IOwnership _out276;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out277;
        (this).GenExpr(_1673_expr, selfIdent, env, expectedOwnership, out _out275, out _out276, out _out277);
        _1676_recursiveGen = _out275;
        _1677_recOwned = _out276;
        _1678_recIdents = _out277;
        r = _1676_recursiveGen;
        RAST._IExpr _out278;
        DCOMP._IOwnership _out279;
        (this).FromOwnership(r, _1677_recOwned, expectedOwnership, out _out278, out _out279);
        r = _out278;
        resultingOwnership = _out279;
        readIdents = _1678_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source87 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1674_fromTpe, _1675_toTpe);
        bool unmatched87 = true;
        if (unmatched87) {
          DAST._IType _1679___v118 = _source87.dtor__0;
          DAST._IType _12 = _source87.dtor__1;
          if (_12.is_UserDefined) {
            DAST._IResolvedType resolved2 = _12.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1680___v119 = resolved2.dtor_path;
            Dafny.ISequence<DAST._IType> _1681___v120 = resolved2.dtor_typeArgs;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1682_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1683_range = kind2.dtor_range;
              bool _1684_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1685_attributes = resolved2.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1686___v121 = resolved2.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1687___v122 = resolved2.dtor_extendedTypes;
              unmatched87 = false;
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
        if (unmatched87) {
          DAST._IType _02 = _source87.dtor__0;
          if (_02.is_UserDefined) {
            DAST._IResolvedType resolved3 = _02.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1688___v123 = resolved3.dtor_path;
            Dafny.ISequence<DAST._IType> _1689___v124 = resolved3.dtor_typeArgs;
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1690_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1691_range = kind3.dtor_range;
              bool _1692_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1693_attributes = resolved3.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1694___v125 = resolved3.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1695___v126 = resolved3.dtor_extendedTypes;
              DAST._IType _1696___v127 = _source87.dtor__1;
              unmatched87 = false;
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
        if (unmatched87) {
          DAST._IType _03 = _source87.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h72 = _03.dtor_Primitive_a0;
            if (_h72.is_Int) {
              DAST._IType _13 = _source87.dtor__1;
              if (_13.is_Primitive) {
                DAST._IPrimitive _h73 = _13.dtor_Primitive_a0;
                if (_h73.is_Real) {
                  unmatched87 = false;
                  {
                    RAST._IExpr _1697_recursiveGen;
                    DCOMP._IOwnership _1698___v128;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1699_recIdents;
                    RAST._IExpr _out286;
                    DCOMP._IOwnership _out287;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out288;
                    (this).GenExpr(_1673_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out286, out _out287, out _out288);
                    _1697_recursiveGen = _out286;
                    _1698___v128 = _out287;
                    _1699_recIdents = _out288;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1697_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out289;
                    DCOMP._IOwnership _out290;
                    (this).FromOwned(r, expectedOwnership, out _out289, out _out290);
                    r = _out289;
                    resultingOwnership = _out290;
                    readIdents = _1699_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched87) {
          DAST._IType _04 = _source87.dtor__0;
          if (_04.is_Primitive) {
            DAST._IPrimitive _h74 = _04.dtor_Primitive_a0;
            if (_h74.is_Real) {
              DAST._IType _14 = _source87.dtor__1;
              if (_14.is_Primitive) {
                DAST._IPrimitive _h75 = _14.dtor_Primitive_a0;
                if (_h75.is_Int) {
                  unmatched87 = false;
                  {
                    RAST._IExpr _1700_recursiveGen;
                    DCOMP._IOwnership _1701___v129;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1702_recIdents;
                    RAST._IExpr _out291;
                    DCOMP._IOwnership _out292;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out293;
                    (this).GenExpr(_1673_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out291, out _out292, out _out293);
                    _1700_recursiveGen = _out291;
                    _1701___v129 = _out292;
                    _1702_recIdents = _out293;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1700_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out294;
                    DCOMP._IOwnership _out295;
                    (this).FromOwned(r, expectedOwnership, out _out294, out _out295);
                    r = _out294;
                    resultingOwnership = _out295;
                    readIdents = _1702_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched87) {
          DAST._IType _05 = _source87.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h76 = _05.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _15 = _source87.dtor__1;
              if (_15.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1703___v130 = _15.dtor_Passthrough_a0;
                unmatched87 = false;
                {
                  RAST._IType _1704_rhsType;
                  RAST._IType _out296;
                  _out296 = (this).GenType(_1675_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1704_rhsType = _out296;
                  RAST._IExpr _1705_recursiveGen;
                  DCOMP._IOwnership _1706___v131;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1707_recIdents;
                  RAST._IExpr _out297;
                  DCOMP._IOwnership _out298;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out299;
                  (this).GenExpr(_1673_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out297, out _out298, out _out299);
                  _1705_recursiveGen = _out297;
                  _1706___v131 = _out298;
                  _1707_recIdents = _out299;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1704_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1705_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out300;
                  DCOMP._IOwnership _out301;
                  (this).FromOwned(r, expectedOwnership, out _out300, out _out301);
                  r = _out300;
                  resultingOwnership = _out301;
                  readIdents = _1707_recIdents;
                }
              }
            }
          }
        }
        if (unmatched87) {
          DAST._IType _06 = _source87.dtor__0;
          if (_06.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1708___v132 = _06.dtor_Passthrough_a0;
            DAST._IType _16 = _source87.dtor__1;
            if (_16.is_Primitive) {
              DAST._IPrimitive _h77 = _16.dtor_Primitive_a0;
              if (_h77.is_Int) {
                unmatched87 = false;
                {
                  RAST._IType _1709_rhsType;
                  RAST._IType _out302;
                  _out302 = (this).GenType(_1674_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1709_rhsType = _out302;
                  RAST._IExpr _1710_recursiveGen;
                  DCOMP._IOwnership _1711___v133;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1712_recIdents;
                  RAST._IExpr _out303;
                  DCOMP._IOwnership _out304;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out305;
                  (this).GenExpr(_1673_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out303, out _out304, out _out305);
                  _1710_recursiveGen = _out303;
                  _1711___v133 = _out304;
                  _1712_recIdents = _out305;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1710_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out306;
                  DCOMP._IOwnership _out307;
                  (this).FromOwned(r, expectedOwnership, out _out306, out _out307);
                  r = _out306;
                  resultingOwnership = _out307;
                  readIdents = _1712_recIdents;
                }
              }
            }
          }
        }
        if (unmatched87) {
          DAST._IType _07 = _source87.dtor__0;
          if (_07.is_Primitive) {
            DAST._IPrimitive _h78 = _07.dtor_Primitive_a0;
            if (_h78.is_Int) {
              DAST._IType _17 = _source87.dtor__1;
              if (_17.is_Primitive) {
                DAST._IPrimitive _h79 = _17.dtor_Primitive_a0;
                if (_h79.is_Char) {
                  unmatched87 = false;
                  {
                    RAST._IType _1713_rhsType;
                    RAST._IType _out308;
                    _out308 = (this).GenType(_1675_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1713_rhsType = _out308;
                    RAST._IExpr _1714_recursiveGen;
                    DCOMP._IOwnership _1715___v134;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1716_recIdents;
                    RAST._IExpr _out309;
                    DCOMP._IOwnership _out310;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out311;
                    (this).GenExpr(_1673_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out309, out _out310, out _out311);
                    _1714_recursiveGen = _out309;
                    _1715___v134 = _out310;
                    _1716_recIdents = _out311;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1714_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out312;
                    DCOMP._IOwnership _out313;
                    (this).FromOwned(r, expectedOwnership, out _out312, out _out313);
                    r = _out312;
                    resultingOwnership = _out313;
                    readIdents = _1716_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched87) {
          DAST._IType _08 = _source87.dtor__0;
          if (_08.is_Primitive) {
            DAST._IPrimitive _h710 = _08.dtor_Primitive_a0;
            if (_h710.is_Char) {
              DAST._IType _18 = _source87.dtor__1;
              if (_18.is_Primitive) {
                DAST._IPrimitive _h711 = _18.dtor_Primitive_a0;
                if (_h711.is_Int) {
                  unmatched87 = false;
                  {
                    RAST._IType _1717_rhsType;
                    RAST._IType _out314;
                    _out314 = (this).GenType(_1674_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1717_rhsType = _out314;
                    RAST._IExpr _1718_recursiveGen;
                    DCOMP._IOwnership _1719___v135;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1720_recIdents;
                    RAST._IExpr _out315;
                    DCOMP._IOwnership _out316;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out317;
                    (this).GenExpr(_1673_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out315, out _out316, out _out317);
                    _1718_recursiveGen = _out315;
                    _1719___v135 = _out316;
                    _1720_recIdents = _out317;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1718_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out318;
                    DCOMP._IOwnership _out319;
                    (this).FromOwned(r, expectedOwnership, out _out318, out _out319);
                    r = _out318;
                    resultingOwnership = _out319;
                    readIdents = _1720_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched87) {
          DAST._IType _09 = _source87.dtor__0;
          if (_09.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1721___v136 = _09.dtor_Passthrough_a0;
            DAST._IType _19 = _source87.dtor__1;
            if (_19.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1722___v137 = _19.dtor_Passthrough_a0;
              unmatched87 = false;
              {
                RAST._IExpr _1723_recursiveGen;
                DCOMP._IOwnership _1724___v138;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1725_recIdents;
                RAST._IExpr _out320;
                DCOMP._IOwnership _out321;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out322;
                (this).GenExpr(_1673_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out320, out _out321, out _out322);
                _1723_recursiveGen = _out320;
                _1724___v138 = _out321;
                _1725_recIdents = _out322;
                RAST._IType _1726_toTpeGen;
                RAST._IType _out323;
                _out323 = (this).GenType(_1675_toTpe, DCOMP.GenTypeContext.InBinding());
                _1726_toTpeGen = _out323;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1723_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1726_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out324;
                DCOMP._IOwnership _out325;
                (this).FromOwned(r, expectedOwnership, out _out324, out _out325);
                r = _out324;
                resultingOwnership = _out325;
                readIdents = _1725_recIdents;
              }
            }
          }
        }
        if (unmatched87) {
          _System._ITuple2<DAST._IType, DAST._IType> _1727___v139 = _source87;
          unmatched87 = false;
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
      Std.Wrappers._IOption<RAST._IType> _1728_tpe;
      _1728_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1729_placeboOpt;
      _1729_placeboOpt = (((_1728_tpe).is_Some) ? (((_1728_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1730_currentlyBorrowed;
      _1730_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1731_noNeedOfClone;
      _1731_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1729_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1730_currentlyBorrowed = false;
        _1731_noNeedOfClone = true;
        _1728_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1729_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_1730_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1728_tpe).is_Some) && (((_1728_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1732_needObjectFromRef;
        _1732_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source88 = (selfIdent).dtor_dafnyType;
          bool unmatched88 = true;
          if (unmatched88) {
            if (_source88.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source88.dtor_resolved;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1733___v140 = resolved4.dtor_path;
              Dafny.ISequence<DAST._IType> _1734___v141 = resolved4.dtor_typeArgs;
              DAST._IResolvedTypeBase _1735_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1736_attributes = resolved4.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1737___v142 = resolved4.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1738___v143 = resolved4.dtor_extendedTypes;
              unmatched88 = false;
              return ((_1735_base).is_Class) || ((_1735_base).is_Trait);
            }
          }
          if (unmatched88) {
            DAST._IType _1739___v144 = _source88;
            unmatched88 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_1732_needObjectFromRef) {
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1731_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1731_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1730_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1728_tpe).is_Some) && (((_1728_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1740_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1740_attributes).UniqueElements, false, (((_exists_var_1) => {
        DAST._IAttribute _1741_attribute = (DAST._IAttribute)_exists_var_1;
        return ((_1740_attributes).Contains(_1741_attribute)) && ((((_1741_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1741_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      for (BigInteger _1742_i = BigInteger.Zero; _1742_i < _hi36; _1742_i++) {
        DCOMP._IOwnership _1743_argOwnership;
        _1743_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if (((name).is_CallName) && ((_1742_i) < (new BigInteger((((name).dtor_signature)).Count)))) {
          RAST._IType _1744_tpe;
          RAST._IType _out329;
          _out329 = (this).GenType(((((name).dtor_signature)).Select(_1742_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1744_tpe = _out329;
          if ((_1744_tpe).CanReadWithoutClone()) {
            _1743_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1745_argExpr;
        DCOMP._IOwnership _1746___v145;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1747_argIdents;
        RAST._IExpr _out330;
        DCOMP._IOwnership _out331;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out332;
        (this).GenExpr((args).Select(_1742_i), selfIdent, env, _1743_argOwnership, out _out330, out _out331, out _out332);
        _1745_argExpr = _out330;
        _1746___v145 = _out331;
        _1747_argIdents = _out332;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1745_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1747_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi37 = new BigInteger((typeArgs).Count);
      for (BigInteger _1748_typeI = BigInteger.Zero; _1748_typeI < _hi37; _1748_typeI++) {
        RAST._IType _1749_typeExpr;
        RAST._IType _out333;
        _out333 = (this).GenType((typeArgs).Select(_1748_typeI), DCOMP.GenTypeContext.@default());
        _1749_typeExpr = _out333;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1749_typeExpr));
      }
      fullNameQualifier = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
        DAST._ICallName _source89 = name;
        bool unmatched89 = true;
        if (unmatched89) {
          if (_source89.is_CallName) {
            Dafny.ISequence<Dafny.Rune> _1750_nameIdent = _source89.dtor_name;
            Std.Wrappers._IOption<DAST._IType> onType1 = _source89.dtor_onType;
            if (onType1.is_Some) {
              DAST._IType value10 = onType1.dtor_value;
              if (value10.is_UserDefined) {
                DAST._IResolvedType _1751_resolvedType = value10.dtor_resolved;
                Std.Wrappers._IOption<DAST._IFormal> _1752___v146 = _source89.dtor_receiverArgs;
                Dafny.ISequence<DAST._IFormal> _1753___v147 = _source89.dtor_signature;
                unmatched89 = false;
                if ((((_1751_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_1754_resolvedType, _1755_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(((_1754_resolvedType).dtor_properMethods).UniqueElements, true, (((_forall_var_5) => {
                  Dafny.ISequence<Dafny.Rune> _1756_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_5;
                  return !(((_1754_resolvedType).dtor_properMethods).Contains(_1756_m)) || (!object.Equals((_1756_m), _1755_nameIdent));
                }))))(_1751_resolvedType, _1750_nameIdent))) {
                  return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_1751_resolvedType, (_1750_nameIdent)), _1751_resolvedType));
                } else {
                  return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
                }
              }
            }
          }
        }
        if (unmatched89) {
          DAST._ICallName _1757___v148 = _source89;
          unmatched89 = false;
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
      DAST._IExpression _source90 = e;
      bool unmatched90 = true;
      if (unmatched90) {
        if (_source90.is_Literal) {
          DAST._ILiteral _1758___v149 = _source90.dtor_Literal_a0;
          unmatched90 = false;
          RAST._IExpr _out334;
          DCOMP._IOwnership _out335;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out336;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out334, out _out335, out _out336);
          r = _out334;
          resultingOwnership = _out335;
          readIdents = _out336;
        }
      }
      if (unmatched90) {
        if (_source90.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1759_name = _source90.dtor_Ident_a0;
          unmatched90 = false;
          {
            RAST._IExpr _out337;
            DCOMP._IOwnership _out338;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out339;
            (this).GenIdent(DCOMP.__default.escapeName(_1759_name), selfIdent, env, expectedOwnership, out _out337, out _out338, out _out339);
            r = _out337;
            resultingOwnership = _out338;
            readIdents = _out339;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1760_path = _source90.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _1761_typeArgs = _source90.dtor_typeArgs;
          unmatched90 = false;
          {
            RAST._IExpr _out340;
            _out340 = DCOMP.COMP.GenPathExpr(_1760_path);
            r = _out340;
            if ((new BigInteger((_1761_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1762_typeExprs;
              _1762_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi38 = new BigInteger((_1761_typeArgs).Count);
              for (BigInteger _1763_i = BigInteger.Zero; _1763_i < _hi38; _1763_i++) {
                RAST._IType _1764_typeExpr;
                RAST._IType _out341;
                _out341 = (this).GenType((_1761_typeArgs).Select(_1763_i), DCOMP.GenTypeContext.@default());
                _1764_typeExpr = _out341;
                _1762_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1762_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1764_typeExpr));
              }
              r = (r).ApplyType(_1762_typeExprs);
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
      if (unmatched90) {
        if (_source90.is_InitializationValue) {
          DAST._IType _1765_typ = _source90.dtor_typ;
          unmatched90 = false;
          {
            RAST._IType _1766_typExpr;
            RAST._IType _out344;
            _out344 = (this).GenType(_1765_typ, DCOMP.GenTypeContext.@default());
            _1766_typExpr = _out344;
            if ((_1766_typExpr).IsObjectOrPointer()) {
              r = (_1766_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1766_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
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
      if (unmatched90) {
        if (_source90.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1767_values = _source90.dtor_Tuple_a0;
          unmatched90 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1768_exprs;
            _1768_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi39 = new BigInteger((_1767_values).Count);
            for (BigInteger _1769_i = BigInteger.Zero; _1769_i < _hi39; _1769_i++) {
              RAST._IExpr _1770_recursiveGen;
              DCOMP._IOwnership _1771___v150;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1772_recIdents;
              RAST._IExpr _out347;
              DCOMP._IOwnership _out348;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out349;
              (this).GenExpr((_1767_values).Select(_1769_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out347, out _out348, out _out349);
              _1770_recursiveGen = _out347;
              _1771___v150 = _out348;
              _1772_recIdents = _out349;
              _1768_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1768_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1770_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1772_recIdents);
            }
            r = (((new BigInteger((_1767_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1768_exprs)) : (RAST.__default.SystemTuple(_1768_exprs)));
            RAST._IExpr _out350;
            DCOMP._IOwnership _out351;
            (this).FromOwned(r, expectedOwnership, out _out350, out _out351);
            r = _out350;
            resultingOwnership = _out351;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1773_path = _source90.dtor_path;
          Dafny.ISequence<DAST._IType> _1774_typeArgs = _source90.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1775_args = _source90.dtor_args;
          unmatched90 = false;
          {
            RAST._IExpr _out352;
            _out352 = DCOMP.COMP.GenPathExpr(_1773_path);
            r = _out352;
            if ((new BigInteger((_1774_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1776_typeExprs;
              _1776_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_1774_typeArgs).Count);
              for (BigInteger _1777_i = BigInteger.Zero; _1777_i < _hi40; _1777_i++) {
                RAST._IType _1778_typeExpr;
                RAST._IType _out353;
                _out353 = (this).GenType((_1774_typeArgs).Select(_1777_i), DCOMP.GenTypeContext.@default());
                _1778_typeExpr = _out353;
                _1776_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1776_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1778_typeExpr));
              }
              r = (r).ApplyType(_1776_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1779_arguments;
            _1779_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi41 = new BigInteger((_1775_args).Count);
            for (BigInteger _1780_i = BigInteger.Zero; _1780_i < _hi41; _1780_i++) {
              RAST._IExpr _1781_recursiveGen;
              DCOMP._IOwnership _1782___v151;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1783_recIdents;
              RAST._IExpr _out354;
              DCOMP._IOwnership _out355;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out356;
              (this).GenExpr((_1775_args).Select(_1780_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out354, out _out355, out _out356);
              _1781_recursiveGen = _out354;
              _1782___v151 = _out355;
              _1783_recIdents = _out356;
              _1779_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1779_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1781_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1783_recIdents);
            }
            r = (r).Apply(_1779_arguments);
            RAST._IExpr _out357;
            DCOMP._IOwnership _out358;
            (this).FromOwned(r, expectedOwnership, out _out357, out _out358);
            r = _out357;
            resultingOwnership = _out358;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _1784_dims = _source90.dtor_dims;
          DAST._IType _1785_typ = _source90.dtor_typ;
          unmatched90 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1784_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1786_msg;
              _1786_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1786_msg);
              }
              r = RAST.Expr.create_RawExpr(_1786_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1787_typeGen;
              RAST._IType _out359;
              _out359 = (this).GenType(_1785_typ, DCOMP.GenTypeContext.@default());
              _1787_typeGen = _out359;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1788_dimExprs;
              _1788_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi42 = new BigInteger((_1784_dims).Count);
              for (BigInteger _1789_i = BigInteger.Zero; _1789_i < _hi42; _1789_i++) {
                RAST._IExpr _1790_recursiveGen;
                DCOMP._IOwnership _1791___v152;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1792_recIdents;
                RAST._IExpr _out360;
                DCOMP._IOwnership _out361;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out362;
                (this).GenExpr((_1784_dims).Select(_1789_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out360, out _out361, out _out362);
                _1790_recursiveGen = _out360;
                _1791___v152 = _out361;
                _1792_recIdents = _out362;
                _1788_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1788_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_TypeAscription(_1790_recursiveGen, RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("usize")))));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1792_recIdents);
              }
              if ((new BigInteger((_1784_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1793_class__name;
                _1793_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1784_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1793_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1787_typeGen))).MSel((this).placebos__usize)).Apply(_1788_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1787_typeGen))).Apply(_1788_dimExprs);
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
      if (unmatched90) {
        if (_source90.is_ArrayIndexToInt) {
          DAST._IExpression _1794_underlying = _source90.dtor_value;
          unmatched90 = false;
          {
            RAST._IExpr _1795_recursiveGen;
            DCOMP._IOwnership _1796___v153;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1797_recIdents;
            RAST._IExpr _out365;
            DCOMP._IOwnership _out366;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out367;
            (this).GenExpr(_1794_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out365, out _out366, out _out367);
            _1795_recursiveGen = _out365;
            _1796___v153 = _out366;
            _1797_recIdents = _out367;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1795_recursiveGen);
            readIdents = _1797_recIdents;
            RAST._IExpr _out368;
            DCOMP._IOwnership _out369;
            (this).FromOwned(r, expectedOwnership, out _out368, out _out369);
            r = _out368;
            resultingOwnership = _out369;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_FinalizeNewArray) {
          DAST._IExpression _1798_underlying = _source90.dtor_value;
          DAST._IType _1799_typ = _source90.dtor_typ;
          unmatched90 = false;
          {
            RAST._IType _1800_tpe;
            RAST._IType _out370;
            _out370 = (this).GenType(_1799_typ, DCOMP.GenTypeContext.@default());
            _1800_tpe = _out370;
            RAST._IExpr _1801_recursiveGen;
            DCOMP._IOwnership _1802___v154;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1803_recIdents;
            RAST._IExpr _out371;
            DCOMP._IOwnership _out372;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out373;
            (this).GenExpr(_1798_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out371, out _out372, out _out373);
            _1801_recursiveGen = _out371;
            _1802___v154 = _out372;
            _1803_recIdents = _out373;
            readIdents = _1803_recIdents;
            if ((_1800_tpe).IsObjectOrPointer()) {
              RAST._IType _1804_t;
              _1804_t = (_1800_tpe).ObjectOrPointerUnderlying();
              if ((_1804_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1801_recursiveGen);
              } else if ((_1804_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1805_c;
                _1805_c = (_1804_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1805_c)).MSel((this).array__construct)).Apply1(_1801_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1800_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1800_tpe)._ToString(DCOMP.__default.IND)));
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
      if (unmatched90) {
        if (_source90.is_DatatypeValue) {
          DAST._IResolvedType _1806_datatypeType = _source90.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1807_typeArgs = _source90.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1808_variant = _source90.dtor_variant;
          bool _1809_isCo = _source90.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1810_values = _source90.dtor_contents;
          unmatched90 = false;
          {
            RAST._IExpr _out376;
            _out376 = DCOMP.COMP.GenPathExpr((_1806_datatypeType).dtor_path);
            r = _out376;
            Dafny.ISequence<RAST._IType> _1811_genTypeArgs;
            _1811_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi43 = new BigInteger((_1807_typeArgs).Count);
            for (BigInteger _1812_i = BigInteger.Zero; _1812_i < _hi43; _1812_i++) {
              RAST._IType _1813_typeExpr;
              RAST._IType _out377;
              _out377 = (this).GenType((_1807_typeArgs).Select(_1812_i), DCOMP.GenTypeContext.@default());
              _1813_typeExpr = _out377;
              _1811_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1811_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1813_typeExpr));
            }
            if ((new BigInteger((_1807_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1811_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1808_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1814_assignments;
            _1814_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi44 = new BigInteger((_1810_values).Count);
            for (BigInteger _1815_i = BigInteger.Zero; _1815_i < _hi44; _1815_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs64 = (_1810_values).Select(_1815_i);
              Dafny.ISequence<Dafny.Rune> _1816_name = _let_tmp_rhs64.dtor__0;
              DAST._IExpression _1817_value = _let_tmp_rhs64.dtor__1;
              if (_1809_isCo) {
                RAST._IExpr _1818_recursiveGen;
                DCOMP._IOwnership _1819___v155;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1820_recIdents;
                RAST._IExpr _out378;
                DCOMP._IOwnership _out379;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out380;
                (this).GenExpr(_1817_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out378, out _out379, out _out380);
                _1818_recursiveGen = _out378;
                _1819___v155 = _out379;
                _1820_recIdents = _out380;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1820_recIdents);
                Dafny.ISequence<Dafny.Rune> _1821_allReadCloned;
                _1821_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1820_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1822_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1820_recIdents).Elements) {
                    _1822_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1820_recIdents).Contains(_1822_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4001)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1821_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1821_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1822_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1822_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1820_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1820_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1822_next));
                }
                Dafny.ISequence<Dafny.Rune> _1823_wasAssigned;
                _1823_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1821_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1818_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1814_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1814_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1816_name), RAST.Expr.create_RawExpr(_1823_wasAssigned))));
              } else {
                RAST._IExpr _1824_recursiveGen;
                DCOMP._IOwnership _1825___v156;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1826_recIdents;
                RAST._IExpr _out381;
                DCOMP._IOwnership _out382;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out383;
                (this).GenExpr(_1817_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out381, out _out382, out _out383);
                _1824_recursiveGen = _out381;
                _1825___v156 = _out382;
                _1826_recIdents = _out383;
                _1814_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1814_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1816_name), _1824_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1826_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1814_assignments);
            if ((this).IsRcWrapped((_1806_datatypeType).dtor_attributes)) {
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
      if (unmatched90) {
        if (_source90.is_Convert) {
          DAST._IExpression _1827___v157 = _source90.dtor_value;
          DAST._IType _1828___v158 = _source90.dtor_from;
          DAST._IType _1829___v159 = _source90.dtor_typ;
          unmatched90 = false;
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
      if (unmatched90) {
        if (_source90.is_SeqConstruct) {
          DAST._IExpression _1830_length = _source90.dtor_length;
          DAST._IExpression _1831_expr = _source90.dtor_elem;
          unmatched90 = false;
          {
            RAST._IExpr _1832_recursiveGen;
            DCOMP._IOwnership _1833___v160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1834_recIdents;
            RAST._IExpr _out389;
            DCOMP._IOwnership _out390;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out391;
            (this).GenExpr(_1831_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out389, out _out390, out _out391);
            _1832_recursiveGen = _out389;
            _1833___v160 = _out390;
            _1834_recIdents = _out391;
            RAST._IExpr _1835_lengthGen;
            DCOMP._IOwnership _1836___v161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1837_lengthIdents;
            RAST._IExpr _out392;
            DCOMP._IOwnership _out393;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out394;
            (this).GenExpr(_1830_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out392, out _out393, out _out394);
            _1835_lengthGen = _out392;
            _1836___v161 = _out393;
            _1837_lengthIdents = _out394;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1832_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1835_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1834_recIdents, _1837_lengthIdents);
            RAST._IExpr _out395;
            DCOMP._IOwnership _out396;
            (this).FromOwned(r, expectedOwnership, out _out395, out _out396);
            r = _out395;
            resultingOwnership = _out396;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _1838_exprs = _source90.dtor_elements;
          DAST._IType _1839_typ = _source90.dtor_typ;
          unmatched90 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1840_genTpe;
            RAST._IType _out397;
            _out397 = (this).GenType(_1839_typ, DCOMP.GenTypeContext.@default());
            _1840_genTpe = _out397;
            BigInteger _1841_i;
            _1841_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1842_args;
            _1842_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1841_i) < (new BigInteger((_1838_exprs).Count))) {
              RAST._IExpr _1843_recursiveGen;
              DCOMP._IOwnership _1844___v162;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1845_recIdents;
              RAST._IExpr _out398;
              DCOMP._IOwnership _out399;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
              (this).GenExpr((_1838_exprs).Select(_1841_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out398, out _out399, out _out400);
              _1843_recursiveGen = _out398;
              _1844___v162 = _out399;
              _1845_recIdents = _out400;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1845_recIdents);
              _1842_args = Dafny.Sequence<RAST._IExpr>.Concat(_1842_args, Dafny.Sequence<RAST._IExpr>.FromElements(_1843_recursiveGen));
              _1841_i = (_1841_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_1842_args);
            if ((new BigInteger((_1842_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1840_genTpe));
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
      if (unmatched90) {
        if (_source90.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _1846_exprs = _source90.dtor_elements;
          unmatched90 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1847_generatedValues;
            _1847_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1848_i;
            _1848_i = BigInteger.Zero;
            while ((_1848_i) < (new BigInteger((_1846_exprs).Count))) {
              RAST._IExpr _1849_recursiveGen;
              DCOMP._IOwnership _1850___v163;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1851_recIdents;
              RAST._IExpr _out403;
              DCOMP._IOwnership _out404;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out405;
              (this).GenExpr((_1846_exprs).Select(_1848_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out403, out _out404, out _out405);
              _1849_recursiveGen = _out403;
              _1850___v163 = _out404;
              _1851_recIdents = _out405;
              _1847_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1847_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1849_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1851_recIdents);
              _1848_i = (_1848_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_1847_generatedValues);
            RAST._IExpr _out406;
            DCOMP._IOwnership _out407;
            (this).FromOwned(r, expectedOwnership, out _out406, out _out407);
            r = _out406;
            resultingOwnership = _out407;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _1852_exprs = _source90.dtor_elements;
          unmatched90 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1853_generatedValues;
            _1853_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1854_i;
            _1854_i = BigInteger.Zero;
            while ((_1854_i) < (new BigInteger((_1852_exprs).Count))) {
              RAST._IExpr _1855_recursiveGen;
              DCOMP._IOwnership _1856___v164;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1857_recIdents;
              RAST._IExpr _out408;
              DCOMP._IOwnership _out409;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out410;
              (this).GenExpr((_1852_exprs).Select(_1854_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out408, out _out409, out _out410);
              _1855_recursiveGen = _out408;
              _1856___v164 = _out409;
              _1857_recIdents = _out410;
              _1853_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_1853_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_1855_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1857_recIdents);
              _1854_i = (_1854_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_1853_generatedValues);
            RAST._IExpr _out411;
            DCOMP._IOwnership _out412;
            (this).FromOwned(r, expectedOwnership, out _out411, out _out412);
            r = _out411;
            resultingOwnership = _out412;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_ToMultiset) {
          DAST._IExpression _1858_expr = _source90.dtor_ToMultiset_a0;
          unmatched90 = false;
          {
            RAST._IExpr _1859_recursiveGen;
            DCOMP._IOwnership _1860___v165;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1861_recIdents;
            RAST._IExpr _out413;
            DCOMP._IOwnership _out414;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out415;
            (this).GenExpr(_1858_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out413, out _out414, out _out415);
            _1859_recursiveGen = _out413;
            _1860___v165 = _out414;
            _1861_recIdents = _out415;
            r = ((_1859_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _1861_recIdents;
            RAST._IExpr _out416;
            DCOMP._IOwnership _out417;
            (this).FromOwned(r, expectedOwnership, out _out416, out _out417);
            r = _out416;
            resultingOwnership = _out417;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _1862_mapElems = _source90.dtor_mapElems;
          unmatched90 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _1863_generatedValues;
            _1863_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _1864_i;
            _1864_i = BigInteger.Zero;
            while ((_1864_i) < (new BigInteger((_1862_mapElems).Count))) {
              RAST._IExpr _1865_recursiveGenKey;
              DCOMP._IOwnership _1866___v166;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1867_recIdentsKey;
              RAST._IExpr _out418;
              DCOMP._IOwnership _out419;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out420;
              (this).GenExpr(((_1862_mapElems).Select(_1864_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out418, out _out419, out _out420);
              _1865_recursiveGenKey = _out418;
              _1866___v166 = _out419;
              _1867_recIdentsKey = _out420;
              RAST._IExpr _1868_recursiveGenValue;
              DCOMP._IOwnership _1869___v167;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1870_recIdentsValue;
              RAST._IExpr _out421;
              DCOMP._IOwnership _out422;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out423;
              (this).GenExpr(((_1862_mapElems).Select(_1864_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out421, out _out422, out _out423);
              _1868_recursiveGenValue = _out421;
              _1869___v167 = _out422;
              _1870_recIdentsValue = _out423;
              _1863_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_1863_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_1865_recursiveGenKey, _1868_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1867_recIdentsKey), _1870_recIdentsValue);
              _1864_i = (_1864_i) + (BigInteger.One);
            }
            _1864_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _1871_arguments;
            _1871_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1864_i) < (new BigInteger((_1863_generatedValues).Count))) {
              RAST._IExpr _1872_genKey;
              _1872_genKey = ((_1863_generatedValues).Select(_1864_i)).dtor__0;
              RAST._IExpr _1873_genValue;
              _1873_genValue = ((_1863_generatedValues).Select(_1864_i)).dtor__1;
              _1871_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1871_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _1872_genKey, _1873_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _1864_i = (_1864_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_1871_arguments);
            RAST._IExpr _out424;
            DCOMP._IOwnership _out425;
            (this).FromOwned(r, expectedOwnership, out _out424, out _out425);
            r = _out424;
            resultingOwnership = _out425;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_SeqUpdate) {
          DAST._IExpression _1874_expr = _source90.dtor_expr;
          DAST._IExpression _1875_index = _source90.dtor_indexExpr;
          DAST._IExpression _1876_value = _source90.dtor_value;
          unmatched90 = false;
          {
            RAST._IExpr _1877_exprR;
            DCOMP._IOwnership _1878___v168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1879_exprIdents;
            RAST._IExpr _out426;
            DCOMP._IOwnership _out427;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out428;
            (this).GenExpr(_1874_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out426, out _out427, out _out428);
            _1877_exprR = _out426;
            _1878___v168 = _out427;
            _1879_exprIdents = _out428;
            RAST._IExpr _1880_indexR;
            DCOMP._IOwnership _1881_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1882_indexIdents;
            RAST._IExpr _out429;
            DCOMP._IOwnership _out430;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out431;
            (this).GenExpr(_1875_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out429, out _out430, out _out431);
            _1880_indexR = _out429;
            _1881_indexOwnership = _out430;
            _1882_indexIdents = _out431;
            RAST._IExpr _1883_valueR;
            DCOMP._IOwnership _1884_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1885_valueIdents;
            RAST._IExpr _out432;
            DCOMP._IOwnership _out433;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out434;
            (this).GenExpr(_1876_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out432, out _out433, out _out434);
            _1883_valueR = _out432;
            _1884_valueOwnership = _out433;
            _1885_valueIdents = _out434;
            r = ((_1877_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1880_indexR, _1883_valueR));
            RAST._IExpr _out435;
            DCOMP._IOwnership _out436;
            (this).FromOwned(r, expectedOwnership, out _out435, out _out436);
            r = _out435;
            resultingOwnership = _out436;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1879_exprIdents, _1882_indexIdents), _1885_valueIdents);
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_MapUpdate) {
          DAST._IExpression _1886_expr = _source90.dtor_expr;
          DAST._IExpression _1887_index = _source90.dtor_indexExpr;
          DAST._IExpression _1888_value = _source90.dtor_value;
          unmatched90 = false;
          {
            RAST._IExpr _1889_exprR;
            DCOMP._IOwnership _1890___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1891_exprIdents;
            RAST._IExpr _out437;
            DCOMP._IOwnership _out438;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out439;
            (this).GenExpr(_1886_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out437, out _out438, out _out439);
            _1889_exprR = _out437;
            _1890___v169 = _out438;
            _1891_exprIdents = _out439;
            RAST._IExpr _1892_indexR;
            DCOMP._IOwnership _1893_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1894_indexIdents;
            RAST._IExpr _out440;
            DCOMP._IOwnership _out441;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out442;
            (this).GenExpr(_1887_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out440, out _out441, out _out442);
            _1892_indexR = _out440;
            _1893_indexOwnership = _out441;
            _1894_indexIdents = _out442;
            RAST._IExpr _1895_valueR;
            DCOMP._IOwnership _1896_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1897_valueIdents;
            RAST._IExpr _out443;
            DCOMP._IOwnership _out444;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out445;
            (this).GenExpr(_1888_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out443, out _out444, out _out445);
            _1895_valueR = _out443;
            _1896_valueOwnership = _out444;
            _1897_valueIdents = _out445;
            r = ((_1889_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1892_indexR, _1895_valueR));
            RAST._IExpr _out446;
            DCOMP._IOwnership _out447;
            (this).FromOwned(r, expectedOwnership, out _out446, out _out447);
            r = _out446;
            resultingOwnership = _out447;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1891_exprIdents, _1894_indexIdents), _1897_valueIdents);
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_This) {
          unmatched90 = false;
          {
            DCOMP._ISelfInfo _source91 = selfIdent;
            bool unmatched91 = true;
            if (unmatched91) {
              if (_source91.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _1898_id = _source91.dtor_rSelfName;
                DAST._IType _1899_dafnyType = _source91.dtor_dafnyType;
                unmatched91 = false;
                {
                  RAST._IExpr _out448;
                  DCOMP._IOwnership _out449;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out450;
                  (this).GenIdent(_1898_id, selfIdent, env, expectedOwnership, out _out448, out _out449, out _out450);
                  r = _out448;
                  resultingOwnership = _out449;
                  readIdents = _out450;
                }
              }
            }
            if (unmatched91) {
              DCOMP._ISelfInfo _1900_None = _source91;
              unmatched91 = false;
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
      if (unmatched90) {
        if (_source90.is_Ite) {
          DAST._IExpression _1901_cond = _source90.dtor_cond;
          DAST._IExpression _1902_t = _source90.dtor_thn;
          DAST._IExpression _1903_f = _source90.dtor_els;
          unmatched90 = false;
          {
            RAST._IExpr _1904_cond;
            DCOMP._IOwnership _1905___v170;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1906_recIdentsCond;
            RAST._IExpr _out453;
            DCOMP._IOwnership _out454;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out455;
            (this).GenExpr(_1901_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out453, out _out454, out _out455);
            _1904_cond = _out453;
            _1905___v170 = _out454;
            _1906_recIdentsCond = _out455;
            RAST._IExpr _1907_fExpr;
            DCOMP._IOwnership _1908_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1909_recIdentsF;
            RAST._IExpr _out456;
            DCOMP._IOwnership _out457;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out458;
            (this).GenExpr(_1903_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out456, out _out457, out _out458);
            _1907_fExpr = _out456;
            _1908_fOwned = _out457;
            _1909_recIdentsF = _out458;
            RAST._IExpr _1910_tExpr;
            DCOMP._IOwnership _1911___v171;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1912_recIdentsT;
            RAST._IExpr _out459;
            DCOMP._IOwnership _out460;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out461;
            (this).GenExpr(_1902_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out459, out _out460, out _out461);
            _1910_tExpr = _out459;
            _1911___v171 = _out460;
            _1912_recIdentsT = _out461;
            r = RAST.Expr.create_IfExpr(_1904_cond, _1910_tExpr, _1907_fExpr);
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out462, out _out463);
            r = _out462;
            resultingOwnership = _out463;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1906_recIdentsCond, _1912_recIdentsT), _1909_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source90.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _1913_e = _source90.dtor_expr;
            DAST.Format._IUnaryOpFormat _1914_format = _source90.dtor_format1;
            unmatched90 = false;
            {
              RAST._IExpr _1915_recursiveGen;
              DCOMP._IOwnership _1916___v172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1917_recIdents;
              RAST._IExpr _out464;
              DCOMP._IOwnership _out465;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out466;
              (this).GenExpr(_1913_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out464, out _out465, out _out466);
              _1915_recursiveGen = _out464;
              _1916___v172 = _out465;
              _1917_recIdents = _out466;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _1915_recursiveGen, _1914_format);
              RAST._IExpr _out467;
              DCOMP._IOwnership _out468;
              (this).FromOwned(r, expectedOwnership, out _out467, out _out468);
              r = _out467;
              resultingOwnership = _out468;
              readIdents = _1917_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source90.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _1918_e = _source90.dtor_expr;
            DAST.Format._IUnaryOpFormat _1919_format = _source90.dtor_format1;
            unmatched90 = false;
            {
              RAST._IExpr _1920_recursiveGen;
              DCOMP._IOwnership _1921___v173;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1922_recIdents;
              RAST._IExpr _out469;
              DCOMP._IOwnership _out470;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out471;
              (this).GenExpr(_1918_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out469, out _out470, out _out471);
              _1920_recursiveGen = _out469;
              _1921___v173 = _out470;
              _1922_recIdents = _out471;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _1920_recursiveGen, _1919_format);
              RAST._IExpr _out472;
              DCOMP._IOwnership _out473;
              (this).FromOwned(r, expectedOwnership, out _out472, out _out473);
              r = _out472;
              resultingOwnership = _out473;
              readIdents = _1922_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source90.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _1923_e = _source90.dtor_expr;
            DAST.Format._IUnaryOpFormat _1924_format = _source90.dtor_format1;
            unmatched90 = false;
            {
              RAST._IExpr _1925_recursiveGen;
              DCOMP._IOwnership _1926_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1927_recIdents;
              RAST._IExpr _out474;
              DCOMP._IOwnership _out475;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out476;
              (this).GenExpr(_1923_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out474, out _out475, out _out476);
              _1925_recursiveGen = _out474;
              _1926_recOwned = _out475;
              _1927_recIdents = _out476;
              r = ((_1925_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out477;
              DCOMP._IOwnership _out478;
              (this).FromOwned(r, expectedOwnership, out _out477, out _out478);
              r = _out477;
              resultingOwnership = _out478;
              readIdents = _1927_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_BinOp) {
          DAST._IBinOp _1928___v174 = _source90.dtor_op;
          DAST._IExpression _1929___v175 = _source90.dtor_left;
          DAST._IExpression _1930___v176 = _source90.dtor_right;
          DAST.Format._IBinaryOpFormat _1931___v177 = _source90.dtor_format2;
          unmatched90 = false;
          RAST._IExpr _out479;
          DCOMP._IOwnership _out480;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out481;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out479, out _out480, out _out481);
          r = _out479;
          resultingOwnership = _out480;
          readIdents = _out481;
        }
      }
      if (unmatched90) {
        if (_source90.is_ArrayLen) {
          DAST._IExpression _1932_expr = _source90.dtor_expr;
          DAST._IType _1933_exprType = _source90.dtor_exprType;
          BigInteger _1934_dim = _source90.dtor_dim;
          bool _1935_native = _source90.dtor_native;
          unmatched90 = false;
          {
            RAST._IExpr _1936_recursiveGen;
            DCOMP._IOwnership _1937___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1938_recIdents;
            RAST._IExpr _out482;
            DCOMP._IOwnership _out483;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out484;
            (this).GenExpr(_1932_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out482, out _out483, out _out484);
            _1936_recursiveGen = _out482;
            _1937___v178 = _out483;
            _1938_recIdents = _out484;
            RAST._IType _1939_arrayType;
            RAST._IType _out485;
            _out485 = (this).GenType(_1933_exprType, DCOMP.GenTypeContext.@default());
            _1939_arrayType = _out485;
            if (!((_1939_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _1940_msg;
              _1940_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_1939_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1940_msg);
              r = RAST.Expr.create_RawExpr(_1940_msg);
            } else {
              RAST._IType _1941_underlying;
              _1941_underlying = (_1939_arrayType).ObjectOrPointerUnderlying();
              if (((_1934_dim).Sign == 0) && ((_1941_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_1936_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_1934_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_1936_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = (((this).read__macro).Apply1(_1936_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Length"), Std.Strings.__default.OfNat(_1934_dim)));
                }
              }
              if (!(_1935_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out486;
            DCOMP._IOwnership _out487;
            (this).FromOwned(r, expectedOwnership, out _out486, out _out487);
            r = _out486;
            resultingOwnership = _out487;
            readIdents = _1938_recIdents;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_MapKeys) {
          DAST._IExpression _1942_expr = _source90.dtor_expr;
          unmatched90 = false;
          {
            RAST._IExpr _1943_recursiveGen;
            DCOMP._IOwnership _1944___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1945_recIdents;
            RAST._IExpr _out488;
            DCOMP._IOwnership _out489;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
            (this).GenExpr(_1942_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out488, out _out489, out _out490);
            _1943_recursiveGen = _out488;
            _1944___v179 = _out489;
            _1945_recIdents = _out490;
            readIdents = _1945_recIdents;
            r = ((_1943_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out491;
            DCOMP._IOwnership _out492;
            (this).FromOwned(r, expectedOwnership, out _out491, out _out492);
            r = _out491;
            resultingOwnership = _out492;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_MapValues) {
          DAST._IExpression _1946_expr = _source90.dtor_expr;
          unmatched90 = false;
          {
            RAST._IExpr _1947_recursiveGen;
            DCOMP._IOwnership _1948___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1949_recIdents;
            RAST._IExpr _out493;
            DCOMP._IOwnership _out494;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out495;
            (this).GenExpr(_1946_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out493, out _out494, out _out495);
            _1947_recursiveGen = _out493;
            _1948___v180 = _out494;
            _1949_recIdents = _out495;
            readIdents = _1949_recIdents;
            r = ((_1947_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out496;
            DCOMP._IOwnership _out497;
            (this).FromOwned(r, expectedOwnership, out _out496, out _out497);
            r = _out496;
            resultingOwnership = _out497;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_SelectFn) {
          DAST._IExpression _1950_on = _source90.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1951_field = _source90.dtor_field;
          bool _1952_isDatatype = _source90.dtor_onDatatype;
          bool _1953_isStatic = _source90.dtor_isStatic;
          BigInteger _1954_arity = _source90.dtor_arity;
          unmatched90 = false;
          {
            RAST._IExpr _1955_onExpr;
            DCOMP._IOwnership _1956_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1957_recIdents;
            RAST._IExpr _out498;
            DCOMP._IOwnership _out499;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out500;
            (this).GenExpr(_1950_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out498, out _out499, out _out500);
            _1955_onExpr = _out498;
            _1956_onOwned = _out499;
            _1957_recIdents = _out500;
            Dafny.ISequence<Dafny.Rune> _1958_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _1959_onString;
            _1959_onString = (_1955_onExpr)._ToString(DCOMP.__default.IND);
            if (_1953_isStatic) {
              _1958_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1959_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_1951_field));
            } else {
              _1958_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _1958_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1958_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _1959_onString), ((object.Equals(_1956_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _1960_args;
              _1960_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _1961_i;
              _1961_i = BigInteger.Zero;
              while ((_1961_i) < (_1954_arity)) {
                if ((_1961_i).Sign == 1) {
                  _1960_args = Dafny.Sequence<Dafny.Rune>.Concat(_1960_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _1960_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1960_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_1961_i));
                _1961_i = (_1961_i) + (BigInteger.One);
              }
              _1958_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1958_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _1960_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _1958_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1958_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_1951_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1960_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _1958_s = Dafny.Sequence<Dafny.Rune>.Concat(_1958_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _1958_s = Dafny.Sequence<Dafny.Rune>.Concat(_1958_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _1962_typeShape;
            _1962_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _1963_i;
            _1963_i = BigInteger.Zero;
            while ((_1963_i) < (_1954_arity)) {
              if ((_1963_i).Sign == 1) {
                _1962_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1962_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _1962_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1962_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _1963_i = (_1963_i) + (BigInteger.One);
            }
            _1962_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_1962_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _1958_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _1958_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _1962_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_1958_s);
            RAST._IExpr _out501;
            DCOMP._IOwnership _out502;
            (this).FromOwned(r, expectedOwnership, out _out501, out _out502);
            r = _out501;
            resultingOwnership = _out502;
            readIdents = _1957_recIdents;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Select) {
          DAST._IExpression expr0 = _source90.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1964_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<DAST._IType> _1965_typeArgs = expr0.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _1966_field = _source90.dtor_field;
            bool _1967_isConstant = _source90.dtor_isConstant;
            bool _1968_isDatatype = _source90.dtor_onDatatype;
            DAST._IType _1969_fieldType = _source90.dtor_fieldType;
            unmatched90 = false;
            {
              RAST._IExpr _1970_onExpr;
              DCOMP._IOwnership _1971_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1972_recIdents;
              RAST._IExpr _out503;
              DCOMP._IOwnership _out504;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out505;
              (this).GenExpr(DAST.Expression.create_Companion(_1964_c, _1965_typeArgs), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out503, out _out504, out _out505);
              _1970_onExpr = _out503;
              _1971_onOwned = _out504;
              _1972_recIdents = _out505;
              r = ((_1970_onExpr).MSel(DCOMP.__default.escapeName(_1966_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out506;
              DCOMP._IOwnership _out507;
              (this).FromOwned(r, expectedOwnership, out _out506, out _out507);
              r = _out506;
              resultingOwnership = _out507;
              readIdents = _1972_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Select) {
          DAST._IExpression _1973_on = _source90.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1974_field = _source90.dtor_field;
          bool _1975_isConstant = _source90.dtor_isConstant;
          bool _1976_isDatatype = _source90.dtor_onDatatype;
          DAST._IType _1977_fieldType = _source90.dtor_fieldType;
          unmatched90 = false;
          {
            if (_1976_isDatatype) {
              RAST._IExpr _1978_onExpr;
              DCOMP._IOwnership _1979_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1980_recIdents;
              RAST._IExpr _out508;
              DCOMP._IOwnership _out509;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out510;
              (this).GenExpr(_1973_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out508, out _out509, out _out510);
              _1978_onExpr = _out508;
              _1979_onOwned = _out509;
              _1980_recIdents = _out510;
              r = ((_1978_onExpr).Sel(DCOMP.__default.escapeName(_1974_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _1981_typ;
              RAST._IType _out511;
              _out511 = (this).GenType(_1977_fieldType, DCOMP.GenTypeContext.@default());
              _1981_typ = _out511;
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out512, out _out513);
              r = _out512;
              resultingOwnership = _out513;
              readIdents = _1980_recIdents;
            } else {
              RAST._IExpr _1982_onExpr;
              DCOMP._IOwnership _1983_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1984_recIdents;
              RAST._IExpr _out514;
              DCOMP._IOwnership _out515;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out516;
              (this).GenExpr(_1973_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out514, out _out515, out _out516);
              _1982_onExpr = _out514;
              _1983_onOwned = _out515;
              _1984_recIdents = _out516;
              r = _1982_onExpr;
              if (!object.Equals(_1982_onExpr, RAST.__default.self)) {
                RAST._IExpr _source92 = _1982_onExpr;
                bool unmatched92 = true;
                if (unmatched92) {
                  if (_source92.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source92.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source92.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name21 = underlying5.dtor_name;
                        if (object.Equals(name21, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          DAST.Format._IUnaryOpFormat _1985___v181 = _source92.dtor_format;
                          unmatched92 = false;
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                        }
                      }
                    }
                  }
                }
                if (unmatched92) {
                  RAST._IExpr _1986___v182 = _source92;
                  unmatched92 = false;
                }
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeName(_1974_field));
              if (_1975_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out517;
              DCOMP._IOwnership _out518;
              (this).FromOwned(r, expectedOwnership, out _out517, out _out518);
              r = _out517;
              resultingOwnership = _out518;
              readIdents = _1984_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Index) {
          DAST._IExpression _1987_on = _source90.dtor_expr;
          DAST._ICollKind _1988_collKind = _source90.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _1989_indices = _source90.dtor_indices;
          unmatched90 = false;
          {
            RAST._IExpr _1990_onExpr;
            DCOMP._IOwnership _1991_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1992_recIdents;
            RAST._IExpr _out519;
            DCOMP._IOwnership _out520;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out521;
            (this).GenExpr(_1987_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out519, out _out520, out _out521);
            _1990_onExpr = _out519;
            _1991_onOwned = _out520;
            _1992_recIdents = _out521;
            readIdents = _1992_recIdents;
            r = _1990_onExpr;
            BigInteger _1993_i;
            _1993_i = BigInteger.Zero;
            while ((_1993_i) < (new BigInteger((_1989_indices).Count))) {
              if (object.Equals(_1988_collKind, DAST.CollKind.create_Array())) {
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              RAST._IExpr _1994_idx;
              DCOMP._IOwnership _1995_idxOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1996_recIdentsIdx;
              RAST._IExpr _out522;
              DCOMP._IOwnership _out523;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out524;
              (this).GenExpr((_1989_indices).Select(_1993_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out522, out _out523, out _out524);
              _1994_idx = _out522;
              _1995_idxOwned = _out523;
              _1996_recIdentsIdx = _out524;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_1994_idx);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1996_recIdentsIdx);
              _1993_i = (_1993_i) + (BigInteger.One);
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
      if (unmatched90) {
        if (_source90.is_IndexRange) {
          DAST._IExpression _1997_on = _source90.dtor_expr;
          bool _1998_isArray = _source90.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _1999_low = _source90.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2000_high = _source90.dtor_high;
          unmatched90 = false;
          {
            RAST._IExpr _2001_onExpr;
            DCOMP._IOwnership _2002_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2003_recIdents;
            RAST._IExpr _out527;
            DCOMP._IOwnership _out528;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out529;
            (this).GenExpr(_1997_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out527, out _out528, out _out529);
            _2001_onExpr = _out527;
            _2002_onOwned = _out528;
            _2003_recIdents = _out529;
            readIdents = _2003_recIdents;
            Dafny.ISequence<Dafny.Rune> _2004_methodName;
            _2004_methodName = (((_1999_low).is_Some) ? ((((_2000_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2000_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2005_arguments;
            _2005_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source93 = _1999_low;
            bool unmatched93 = true;
            if (unmatched93) {
              if (_source93.is_Some) {
                DAST._IExpression _2006_l = _source93.dtor_value;
                unmatched93 = false;
                {
                  RAST._IExpr _2007_lExpr;
                  DCOMP._IOwnership _2008___v183;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2009_recIdentsL;
                  RAST._IExpr _out530;
                  DCOMP._IOwnership _out531;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out532;
                  (this).GenExpr(_2006_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out530, out _out531, out _out532);
                  _2007_lExpr = _out530;
                  _2008___v183 = _out531;
                  _2009_recIdentsL = _out532;
                  _2005_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2005_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2007_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2009_recIdentsL);
                }
              }
            }
            if (unmatched93) {
              unmatched93 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source94 = _2000_high;
            bool unmatched94 = true;
            if (unmatched94) {
              if (_source94.is_Some) {
                DAST._IExpression _2010_h = _source94.dtor_value;
                unmatched94 = false;
                {
                  RAST._IExpr _2011_hExpr;
                  DCOMP._IOwnership _2012___v184;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2013_recIdentsH;
                  RAST._IExpr _out533;
                  DCOMP._IOwnership _out534;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out535;
                  (this).GenExpr(_2010_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out533, out _out534, out _out535);
                  _2011_hExpr = _out533;
                  _2012___v184 = _out534;
                  _2013_recIdentsH = _out535;
                  _2005_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2005_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2011_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2013_recIdentsH);
                }
              }
            }
            if (unmatched94) {
              unmatched94 = false;
            }
            r = _2001_onExpr;
            if (_1998_isArray) {
              if (!(_2004_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2004_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2004_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2004_methodName))).Apply(_2005_arguments);
            } else {
              if (!(_2004_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2004_methodName)).Apply(_2005_arguments);
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
      if (unmatched90) {
        if (_source90.is_TupleSelect) {
          DAST._IExpression _2014_on = _source90.dtor_expr;
          BigInteger _2015_idx = _source90.dtor_index;
          DAST._IType _2016_fieldType = _source90.dtor_fieldType;
          unmatched90 = false;
          {
            RAST._IExpr _2017_onExpr;
            DCOMP._IOwnership _2018_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2019_recIdents;
            RAST._IExpr _out538;
            DCOMP._IOwnership _out539;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out540;
            (this).GenExpr(_2014_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out538, out _out539, out _out540);
            _2017_onExpr = _out538;
            _2018_onOwnership = _out539;
            _2019_recIdents = _out540;
            Dafny.ISequence<Dafny.Rune> _2020_selName;
            _2020_selName = Std.Strings.__default.OfNat(_2015_idx);
            DAST._IType _source95 = _2016_fieldType;
            bool unmatched95 = true;
            if (unmatched95) {
              if (_source95.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2021_tps = _source95.dtor_Tuple_a0;
                unmatched95 = false;
                if (((_2016_fieldType).is_Tuple) && ((new BigInteger((_2021_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2020_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2020_selName);
                }
              }
            }
            if (unmatched95) {
              DAST._IType _2022___v185 = _source95;
              unmatched95 = false;
            }
            r = (_2017_onExpr).Sel(_2020_selName);
            RAST._IExpr _out541;
            DCOMP._IOwnership _out542;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out541, out _out542);
            r = _out541;
            resultingOwnership = _out542;
            readIdents = _2019_recIdents;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Call) {
          DAST._IExpression _2023_on = _source90.dtor_on;
          DAST._ICallName _2024_name = _source90.dtor_callName;
          Dafny.ISequence<DAST._IType> _2025_typeArgs = _source90.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2026_args = _source90.dtor_args;
          unmatched90 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2027_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2028_recIdents;
            Dafny.ISequence<RAST._IType> _2029_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2030_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out543;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
            Dafny.ISequence<RAST._IType> _out545;
            Std.Wrappers._IOption<DAST._IResolvedType> _out546;
            (this).GenArgs(selfIdent, _2024_name, _2025_typeArgs, _2026_args, env, out _out543, out _out544, out _out545, out _out546);
            _2027_argExprs = _out543;
            _2028_recIdents = _out544;
            _2029_typeExprs = _out545;
            _2030_fullNameQualifier = _out546;
            readIdents = _2028_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source96 = _2030_fullNameQualifier;
            bool unmatched96 = true;
            if (unmatched96) {
              if (_source96.is_Some) {
                DAST._IResolvedType value11 = _source96.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2031_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2032_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2033_base = value11.dtor_kind;
                Dafny.ISequence<DAST._IAttribute> _2034___v186 = value11.dtor_attributes;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2035___v187 = value11.dtor_properMethods;
                Dafny.ISequence<DAST._IType> _2036___v188 = value11.dtor_extendedTypes;
                unmatched96 = false;
                RAST._IExpr _2037_fullPath;
                RAST._IExpr _out547;
                _out547 = DCOMP.COMP.GenPathExpr(_2031_path);
                _2037_fullPath = _out547;
                Dafny.ISequence<RAST._IType> _2038_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out548;
                _out548 = (this).GenTypeArgs(_2032_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2038_onTypeExprs = _out548;
                RAST._IExpr _2039_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2040_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2041_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2033_base).is_Trait) || ((_2033_base).is_Class)) {
                  RAST._IExpr _out549;
                  DCOMP._IOwnership _out550;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out551;
                  (this).GenExpr(_2023_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out549, out _out550, out _out551);
                  _2039_onExpr = _out549;
                  _2040_recOwnership = _out550;
                  _2041_recIdents = _out551;
                  _2039_onExpr = ((this).read__macro).Apply1(_2039_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2041_recIdents);
                } else {
                  RAST._IExpr _out552;
                  DCOMP._IOwnership _out553;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out554;
                  (this).GenExpr(_2023_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out552, out _out553, out _out554);
                  _2039_onExpr = _out552;
                  _2040_recOwnership = _out553;
                  _2041_recIdents = _out554;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2041_recIdents);
                }
                r = ((((_2037_fullPath).ApplyType(_2038_onTypeExprs)).MSel(DCOMP.__default.escapeName((_2024_name).dtor_name))).ApplyType(_2029_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2039_onExpr), _2027_argExprs));
                RAST._IExpr _out555;
                DCOMP._IOwnership _out556;
                (this).FromOwned(r, expectedOwnership, out _out555, out _out556);
                r = _out555;
                resultingOwnership = _out556;
              }
            }
            if (unmatched96) {
              Std.Wrappers._IOption<DAST._IResolvedType> _2042___v189 = _source96;
              unmatched96 = false;
              RAST._IExpr _2043_onExpr;
              DCOMP._IOwnership _2044___v190;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2045_recIdents;
              RAST._IExpr _out557;
              DCOMP._IOwnership _out558;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out559;
              (this).GenExpr(_2023_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out557, out _out558, out _out559);
              _2043_onExpr = _out557;
              _2044___v190 = _out558;
              _2045_recIdents = _out559;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2045_recIdents);
              Dafny.ISequence<Dafny.Rune> _2046_renderedName;
              _2046_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
                DAST._ICallName _source97 = _2024_name;
                bool unmatched97 = true;
                if (unmatched97) {
                  if (_source97.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _2047_ident = _source97.dtor_name;
                    Std.Wrappers._IOption<DAST._IType> _2048___v191 = _source97.dtor_onType;
                    Std.Wrappers._IOption<DAST._IFormal> _2049___v192 = _source97.dtor_receiverArgs;
                    Dafny.ISequence<DAST._IFormal> _2050___v193 = _source97.dtor_signature;
                    unmatched97 = false;
                    return DCOMP.__default.escapeName(_2047_ident);
                  }
                }
                if (unmatched97) {
                  bool disjunctiveMatch13 = false;
                  if (_source97.is_MapBuilderAdd) {
                    disjunctiveMatch13 = true;
                  }
                  if (_source97.is_SetBuilderAdd) {
                    disjunctiveMatch13 = true;
                  }
                  if (disjunctiveMatch13) {
                    unmatched97 = false;
                    return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  }
                }
                if (unmatched97) {
                  bool disjunctiveMatch14 = false;
                  disjunctiveMatch14 = true;
                  disjunctiveMatch14 = true;
                  if (disjunctiveMatch14) {
                    unmatched97 = false;
                    return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                  }
                }
                throw new System.Exception("unexpected control point");
              }))();
              DAST._IExpression _source98 = _2023_on;
              bool unmatched98 = true;
              if (unmatched98) {
                if (_source98.is_Companion) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2051___v194 = _source98.dtor_Companion_a0;
                  Dafny.ISequence<DAST._IType> _2052___v195 = _source98.dtor_typeArgs;
                  unmatched98 = false;
                  {
                    _2043_onExpr = (_2043_onExpr).MSel(_2046_renderedName);
                  }
                }
              }
              if (unmatched98) {
                DAST._IExpression _2053___v196 = _source98;
                unmatched98 = false;
                {
                  if (!object.Equals(_2043_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source99 = _2024_name;
                    bool unmatched99 = true;
                    if (unmatched99) {
                      if (_source99.is_CallName) {
                        Dafny.ISequence<Dafny.Rune> _2054___v197 = _source99.dtor_name;
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source99.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2055_tpe = onType2.dtor_value;
                          Std.Wrappers._IOption<DAST._IFormal> _2056___v198 = _source99.dtor_receiverArgs;
                          Dafny.ISequence<DAST._IFormal> _2057___v199 = _source99.dtor_signature;
                          unmatched99 = false;
                          RAST._IType _2058_typ;
                          RAST._IType _out560;
                          _out560 = (this).GenType(_2055_tpe, DCOMP.GenTypeContext.@default());
                          _2058_typ = _out560;
                          if ((_2058_typ).IsObjectOrPointer()) {
                            _2043_onExpr = ((this).read__macro).Apply1(_2043_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched99) {
                      DAST._ICallName _2059___v200 = _source99;
                      unmatched99 = false;
                    }
                  }
                  _2043_onExpr = (_2043_onExpr).Sel(_2046_renderedName);
                }
              }
              r = ((_2043_onExpr).ApplyType(_2029_typeExprs)).Apply(_2027_argExprs);
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
      if (unmatched90) {
        if (_source90.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2060_paramsDafny = _source90.dtor_params;
          DAST._IType _2061_retType = _source90.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2062_body = _source90.dtor_body;
          unmatched90 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2063_params;
            Dafny.ISequence<RAST._IFormal> _out563;
            _out563 = (this).GenParams(_2060_paramsDafny);
            _2063_params = _out563;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2064_paramNames;
            _2064_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2065_paramTypesMap;
            _2065_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi45 = new BigInteger((_2063_params).Count);
            for (BigInteger _2066_i = BigInteger.Zero; _2066_i < _hi45; _2066_i++) {
              Dafny.ISequence<Dafny.Rune> _2067_name;
              _2067_name = ((_2063_params).Select(_2066_i)).dtor_name;
              _2064_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2064_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2067_name));
              _2065_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2065_paramTypesMap, _2067_name, ((_2063_params).Select(_2066_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2068_subEnv;
            _2068_subEnv = (env).merge(DCOMP.Environment.create(_2064_paramNames, _2065_paramTypesMap));
            RAST._IExpr _2069_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2070_recIdents;
            DCOMP._IEnvironment _2071___v201;
            RAST._IExpr _out564;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out565;
            DCOMP._IEnvironment _out566;
            (this).GenStmts(_2062_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2068_subEnv, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out564, out _out565, out _out566);
            _2069_recursiveGen = _out564;
            _2070_recIdents = _out565;
            _2071___v201 = _out566;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2070_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2070_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2072_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll6 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in (_2072_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2073_name = (Dafny.ISequence<Dafny.Rune>)_compr_6;
                if ((_2072_paramNames).Contains(_2073_name)) {
                  _coll6.Add(_2073_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll6);
            }))())(_2064_paramNames));
            RAST._IExpr _2074_allReadCloned;
            _2074_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2070_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2075_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2070_recIdents).Elements) {
                _2075_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_2070_recIdents).Contains(_2075_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 4463)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2075_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2076_selfCloned;
                DCOMP._IOwnership _2077___v202;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2078___v203;
                RAST._IExpr _out567;
                DCOMP._IOwnership _out568;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out569;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out567, out _out568, out _out569);
                _2076_selfCloned = _out567;
                _2077___v202 = _out568;
                _2078___v203 = _out569;
                _2074_allReadCloned = (_2074_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2076_selfCloned)));
              } else if (!((_2064_paramNames).Contains(_2075_next))) {
                RAST._IExpr _2079_copy;
                _2079_copy = (RAST.Expr.create_Identifier(_2075_next)).Clone();
                _2074_allReadCloned = (_2074_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2075_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2079_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2075_next));
              }
              _2070_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2070_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2075_next));
            }
            RAST._IType _2080_retTypeGen;
            RAST._IType _out570;
            _out570 = (this).GenType(_2061_retType, DCOMP.GenTypeContext.InFn());
            _2080_retTypeGen = _out570;
            r = RAST.Expr.create_Block((_2074_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2063_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2080_retTypeGen), RAST.Expr.create_Block(_2069_recursiveGen)))));
            RAST._IExpr _out571;
            DCOMP._IOwnership _out572;
            (this).FromOwned(r, expectedOwnership, out _out571, out _out572);
            r = _out571;
            resultingOwnership = _out572;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2081_values = _source90.dtor_values;
          DAST._IType _2082_retType = _source90.dtor_retType;
          DAST._IExpression _2083_expr = _source90.dtor_expr;
          unmatched90 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2084_paramNames;
            _2084_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2085_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out573;
            _out573 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2086_value) => {
              return (_2086_value).dtor__0;
            })), _2081_values));
            _2085_paramFormals = _out573;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2087_paramTypes;
            _2087_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2088_paramNamesSet;
            _2088_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi46 = new BigInteger((_2081_values).Count);
            for (BigInteger _2089_i = BigInteger.Zero; _2089_i < _hi46; _2089_i++) {
              Dafny.ISequence<Dafny.Rune> _2090_name;
              _2090_name = (((_2081_values).Select(_2089_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2091_rName;
              _2091_rName = DCOMP.__default.escapeName(_2090_name);
              _2084_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2084_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2091_rName));
              _2087_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2087_paramTypes, _2091_rName, ((_2085_paramFormals).Select(_2089_i)).dtor_tpe);
              _2088_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2088_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2091_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi47 = new BigInteger((_2081_values).Count);
            for (BigInteger _2092_i = BigInteger.Zero; _2092_i < _hi47; _2092_i++) {
              RAST._IType _2093_typeGen;
              RAST._IType _out574;
              _out574 = (this).GenType((((_2081_values).Select(_2092_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2093_typeGen = _out574;
              RAST._IExpr _2094_valueGen;
              DCOMP._IOwnership _2095___v204;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2096_recIdents;
              RAST._IExpr _out575;
              DCOMP._IOwnership _out576;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out577;
              (this).GenExpr(((_2081_values).Select(_2092_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out575, out _out576, out _out577);
              _2094_valueGen = _out575;
              _2095___v204 = _out576;
              _2096_recIdents = _out577;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_2081_values).Select(_2092_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2093_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2094_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2096_recIdents);
            }
            DCOMP._IEnvironment _2097_newEnv;
            _2097_newEnv = DCOMP.Environment.create(_2084_paramNames, _2087_paramTypes);
            RAST._IExpr _2098_recGen;
            DCOMP._IOwnership _2099_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2100_recIdents;
            RAST._IExpr _out578;
            DCOMP._IOwnership _out579;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out580;
            (this).GenExpr(_2083_expr, selfIdent, _2097_newEnv, expectedOwnership, out _out578, out _out579, out _out580);
            _2098_recGen = _out578;
            _2099_recOwned = _out579;
            _2100_recIdents = _out580;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2100_recIdents, _2088_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2098_recGen));
            RAST._IExpr _out581;
            DCOMP._IOwnership _out582;
            (this).FromOwnership(r, _2099_recOwned, expectedOwnership, out _out581, out _out582);
            r = _out581;
            resultingOwnership = _out582;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2101_name = _source90.dtor_name;
          DAST._IType _2102_tpe = _source90.dtor_typ;
          DAST._IExpression _2103_value = _source90.dtor_value;
          DAST._IExpression _2104_iifeBody = _source90.dtor_iifeBody;
          unmatched90 = false;
          {
            RAST._IExpr _2105_valueGen;
            DCOMP._IOwnership _2106___v205;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2107_recIdents;
            RAST._IExpr _out583;
            DCOMP._IOwnership _out584;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out585;
            (this).GenExpr(_2103_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out583, out _out584, out _out585);
            _2105_valueGen = _out583;
            _2106___v205 = _out584;
            _2107_recIdents = _out585;
            readIdents = _2107_recIdents;
            RAST._IType _2108_valueTypeGen;
            RAST._IType _out586;
            _out586 = (this).GenType(_2102_tpe, DCOMP.GenTypeContext.InFn());
            _2108_valueTypeGen = _out586;
            RAST._IExpr _2109_bodyGen;
            DCOMP._IOwnership _2110___v206;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2111_bodyIdents;
            RAST._IExpr _out587;
            DCOMP._IOwnership _out588;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
            (this).GenExpr(_2104_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out587, out _out588, out _out589);
            _2109_bodyGen = _out587;
            _2110___v206 = _out588;
            _2111_bodyIdents = _out589;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2111_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_2101_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_2101_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_2108_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2105_valueGen))).Then(_2109_bodyGen));
            RAST._IExpr _out590;
            DCOMP._IOwnership _out591;
            (this).FromOwned(r, expectedOwnership, out _out590, out _out591);
            r = _out590;
            resultingOwnership = _out591;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_Apply) {
          DAST._IExpression _2112_func = _source90.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2113_args = _source90.dtor_args;
          unmatched90 = false;
          {
            RAST._IExpr _2114_funcExpr;
            DCOMP._IOwnership _2115___v207;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2116_recIdents;
            RAST._IExpr _out592;
            DCOMP._IOwnership _out593;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
            (this).GenExpr(_2112_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out592, out _out593, out _out594);
            _2114_funcExpr = _out592;
            _2115___v207 = _out593;
            _2116_recIdents = _out594;
            readIdents = _2116_recIdents;
            Dafny.ISequence<RAST._IExpr> _2117_rArgs;
            _2117_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi48 = new BigInteger((_2113_args).Count);
            for (BigInteger _2118_i = BigInteger.Zero; _2118_i < _hi48; _2118_i++) {
              RAST._IExpr _2119_argExpr;
              DCOMP._IOwnership _2120_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2121_argIdents;
              RAST._IExpr _out595;
              DCOMP._IOwnership _out596;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out597;
              (this).GenExpr((_2113_args).Select(_2118_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out595, out _out596, out _out597);
              _2119_argExpr = _out595;
              _2120_argOwned = _out596;
              _2121_argIdents = _out597;
              _2117_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2117_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2119_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2121_argIdents);
            }
            r = (_2114_funcExpr).Apply(_2117_rArgs);
            RAST._IExpr _out598;
            DCOMP._IOwnership _out599;
            (this).FromOwned(r, expectedOwnership, out _out598, out _out599);
            r = _out598;
            resultingOwnership = _out599;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_TypeTest) {
          DAST._IExpression _2122_on = _source90.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2123_dType = _source90.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2124_variant = _source90.dtor_variant;
          unmatched90 = false;
          {
            RAST._IExpr _2125_exprGen;
            DCOMP._IOwnership _2126___v208;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2127_recIdents;
            RAST._IExpr _out600;
            DCOMP._IOwnership _out601;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out602;
            (this).GenExpr(_2122_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out600, out _out601, out _out602);
            _2125_exprGen = _out600;
            _2126___v208 = _out601;
            _2127_recIdents = _out602;
            RAST._IType _2128_dTypePath;
            RAST._IType _out603;
            _out603 = DCOMP.COMP.GenPath(_2123_dType);
            _2128_dTypePath = _out603;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2125_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2128_dTypePath).MSel(DCOMP.__default.escapeName(_2124_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out604;
            DCOMP._IOwnership _out605;
            (this).FromOwned(r, expectedOwnership, out _out604, out _out605);
            r = _out604;
            resultingOwnership = _out605;
            readIdents = _2127_recIdents;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_BoolBoundedPool) {
          unmatched90 = false;
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
      if (unmatched90) {
        if (_source90.is_SetBoundedPool) {
          DAST._IExpression _2129_of = _source90.dtor_of;
          unmatched90 = false;
          {
            RAST._IExpr _2130_exprGen;
            DCOMP._IOwnership _2131___v209;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2132_recIdents;
            RAST._IExpr _out608;
            DCOMP._IOwnership _out609;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out610;
            (this).GenExpr(_2129_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out608, out _out609, out _out610);
            _2130_exprGen = _out608;
            _2131___v209 = _out609;
            _2132_recIdents = _out610;
            r = ((_2130_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out611;
            DCOMP._IOwnership _out612;
            (this).FromOwned(r, expectedOwnership, out _out611, out _out612);
            r = _out611;
            resultingOwnership = _out612;
            readIdents = _2132_recIdents;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_SeqBoundedPool) {
          DAST._IExpression _2133_of = _source90.dtor_of;
          bool _2134_includeDuplicates = _source90.dtor_includeDuplicates;
          unmatched90 = false;
          {
            RAST._IExpr _2135_exprGen;
            DCOMP._IOwnership _2136___v210;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2137_recIdents;
            RAST._IExpr _out613;
            DCOMP._IOwnership _out614;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out615;
            (this).GenExpr(_2133_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out613, out _out614, out _out615);
            _2135_exprGen = _out613;
            _2136___v210 = _out614;
            _2137_recIdents = _out615;
            r = ((_2135_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2134_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out616;
            DCOMP._IOwnership _out617;
            (this).FromOwned(r, expectedOwnership, out _out616, out _out617);
            r = _out616;
            resultingOwnership = _out617;
            readIdents = _2137_recIdents;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_MapBoundedPool) {
          DAST._IExpression _2138_of = _source90.dtor_of;
          unmatched90 = false;
          {
            RAST._IExpr _2139_exprGen;
            DCOMP._IOwnership _2140___v211;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2141_recIdents;
            RAST._IExpr _out618;
            DCOMP._IOwnership _out619;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out620;
            (this).GenExpr(_2138_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out618, out _out619, out _out620);
            _2139_exprGen = _out618;
            _2140___v211 = _out619;
            _2141_recIdents = _out620;
            r = ((((_2139_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2141_recIdents;
            RAST._IExpr _out621;
            DCOMP._IOwnership _out622;
            (this).FromOwned(r, expectedOwnership, out _out621, out _out622);
            r = _out621;
            resultingOwnership = _out622;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_IntRange) {
          DAST._IExpression _2142_lo = _source90.dtor_lo;
          DAST._IExpression _2143_hi = _source90.dtor_hi;
          bool _2144_up = _source90.dtor_up;
          unmatched90 = false;
          {
            RAST._IExpr _2145_lo;
            DCOMP._IOwnership _2146___v212;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2147_recIdentsLo;
            RAST._IExpr _out623;
            DCOMP._IOwnership _out624;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out625;
            (this).GenExpr(_2142_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out623, out _out624, out _out625);
            _2145_lo = _out623;
            _2146___v212 = _out624;
            _2147_recIdentsLo = _out625;
            RAST._IExpr _2148_hi;
            DCOMP._IOwnership _2149___v213;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2150_recIdentsHi;
            RAST._IExpr _out626;
            DCOMP._IOwnership _out627;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out628;
            (this).GenExpr(_2143_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out626, out _out627, out _out628);
            _2148_hi = _out626;
            _2149___v213 = _out627;
            _2150_recIdentsHi = _out628;
            if (_2144_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2145_lo, _2148_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2148_hi, _2145_lo));
            }
            RAST._IExpr _out629;
            DCOMP._IOwnership _out630;
            (this).FromOwned(r, expectedOwnership, out _out629, out _out630);
            r = _out629;
            resultingOwnership = _out630;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2147_recIdentsLo, _2150_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_UnboundedIntRange) {
          DAST._IExpression _2151_start = _source90.dtor_start;
          bool _2152_up = _source90.dtor_up;
          unmatched90 = false;
          {
            RAST._IExpr _2153_start;
            DCOMP._IOwnership _2154___v214;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2155_recIdentStart;
            RAST._IExpr _out631;
            DCOMP._IOwnership _out632;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out633;
            (this).GenExpr(_2151_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out631, out _out632, out _out633);
            _2153_start = _out631;
            _2154___v214 = _out632;
            _2155_recIdentStart = _out633;
            if (_2152_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2153_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2153_start);
            }
            RAST._IExpr _out634;
            DCOMP._IOwnership _out635;
            (this).FromOwned(r, expectedOwnership, out _out634, out _out635);
            r = _out634;
            resultingOwnership = _out635;
            readIdents = _2155_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched90) {
        if (_source90.is_MapBuilder) {
          DAST._IType _2156_keyType = _source90.dtor_keyType;
          DAST._IType _2157_valueType = _source90.dtor_valueType;
          unmatched90 = false;
          {
            RAST._IType _2158_kType;
            RAST._IType _out636;
            _out636 = (this).GenType(_2156_keyType, DCOMP.GenTypeContext.@default());
            _2158_kType = _out636;
            RAST._IType _2159_vType;
            RAST._IType _out637;
            _out637 = (this).GenType(_2157_valueType, DCOMP.GenTypeContext.@default());
            _2159_vType = _out637;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2158_kType, _2159_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
      if (unmatched90) {
        if (_source90.is_SetBuilder) {
          DAST._IType _2160_elemType = _source90.dtor_elemType;
          unmatched90 = false;
          {
            RAST._IType _2161_eType;
            RAST._IType _out640;
            _out640 = (this).GenType(_2160_elemType, DCOMP.GenTypeContext.@default());
            _2161_eType = _out640;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2161_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out641;
            DCOMP._IOwnership _out642;
            (this).FromOwned(r, expectedOwnership, out _out641, out _out642);
            r = _out641;
            resultingOwnership = _out642;
            return ;
          }
        }
      }
      if (unmatched90) {
        DAST._IType _2162_elemType = _source90.dtor_elemType;
        DAST._IExpression _2163_collection = _source90.dtor_collection;
        bool _2164_is__forall = _source90.dtor_is__forall;
        DAST._IExpression _2165_lambda = _source90.dtor_lambda;
        unmatched90 = false;
        {
          RAST._IType _2166_tpe;
          RAST._IType _out643;
          _out643 = (this).GenType(_2162_elemType, DCOMP.GenTypeContext.@default());
          _2166_tpe = _out643;
          RAST._IExpr _2167_collectionGen;
          DCOMP._IOwnership _2168___v215;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2169_recIdents;
          RAST._IExpr _out644;
          DCOMP._IOwnership _out645;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out646;
          (this).GenExpr(_2163_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out644, out _out645, out _out646);
          _2167_collectionGen = _out644;
          _2168___v215 = _out645;
          _2169_recIdents = _out646;
          Dafny.ISequence<DAST._IAttribute> _2170_extraAttributes;
          _2170_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2163_collection).is_IntRange) || ((_2163_collection).is_UnboundedIntRange)) || ((_2163_collection).is_SeqBoundedPool)) {
            _2170_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2165_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2171_formals;
            _2171_formals = (_2165_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2172_newFormals;
            _2172_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi49 = new BigInteger((_2171_formals).Count);
            for (BigInteger _2173_i = BigInteger.Zero; _2173_i < _hi49; _2173_i++) {
              var _pat_let_tv111 = _2170_extraAttributes;
              var _pat_let_tv112 = _2171_formals;
              _2172_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2172_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2171_formals).Select(_2173_i), _pat_let36_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let36_0, _2174_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv111, ((_pat_let_tv112).Select(_2173_i)).dtor_attributes), _pat_let37_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let37_0, _2175_dt__update_hattributes_h0 => DAST.Formal.create((_2174_dt__update__tmp_h0).dtor_name, (_2174_dt__update__tmp_h0).dtor_typ, _2175_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv113 = _2172_newFormals;
            DAST._IExpression _2176_newLambda;
            _2176_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2165_lambda, _pat_let38_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let38_0, _2177_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv113, _pat_let39_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let39_0, _2178_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2178_dt__update_hparams_h0, (_2177_dt__update__tmp_h1).dtor_retType, (_2177_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2179_lambdaGen;
            DCOMP._IOwnership _2180___v216;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2181_recLambdaIdents;
            RAST._IExpr _out647;
            DCOMP._IOwnership _out648;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out649;
            (this).GenExpr(_2176_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out647, out _out648, out _out649);
            _2179_lambdaGen = _out647;
            _2180___v216 = _out648;
            _2181_recLambdaIdents = _out649;
            Dafny.ISequence<Dafny.Rune> _2182_fn;
            _2182_fn = ((_2164_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2167_collectionGen).Sel(_2182_fn)).Apply1(((_2179_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2169_recIdents, _2181_recLambdaIdents);
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
      BigInteger _2183_i;
      _2183_i = BigInteger.Zero;
      while ((_2183_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2184_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _2185_m;
        RAST._IMod _out652;
        _out652 = (this).GenModule((p).Select(_2183_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2185_m = _out652;
        _2184_generated = (_2185_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_2183_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2184_generated);
        _2183_i = (_2183_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2186_i;
      _2186_i = BigInteger.Zero;
      while ((_2186_i) < (new BigInteger((fullName).Count))) {
        if ((_2186_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2186_i)));
        _2186_i = (_2186_i) + (BigInteger.One);
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