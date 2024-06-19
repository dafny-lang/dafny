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
      Dafny.ISequence<Dafny.Rune> _1148___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1148___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('_'))) {
        _1148___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1148___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"));
        Dafny.ISequence<Dafny.Rune> _in123 = (i).Drop(new BigInteger(2));
        i = _in123;
        goto TAIL_CALL_START;
      } else {
        _1148___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1148___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in124 = (i).Drop(BigInteger.One);
        i = _in124;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.Rune> replaceDots(Dafny.ISequence<Dafny.Rune> i) {
      Dafny.ISequence<Dafny.Rune> _1149___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((i).Count)).Sign == 0) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_1149___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      } else if (((i).Select(BigInteger.Zero)) == (new Dafny.Rune('.'))) {
        _1149___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1149___accumulator, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_d"));
        Dafny.ISequence<Dafny.Rune> _in125 = (i).Drop(BigInteger.One);
        i = _in125;
        goto TAIL_CALL_START;
      } else {
        _1149___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_1149___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((i).Select(BigInteger.Zero)));
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
        Dafny.ISequence<Dafny.Rune> _1150_r = DCOMP.__default.replaceDots(i);
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1150_r);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeField(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1151_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1151_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("r#_"), _1151_r);
      } else {
        return DCOMP.__default.escapeName(f);
      }
    }
    public static Dafny.ISequence<Dafny.Rune> escapeDtor(Dafny.ISequence<Dafny.Rune> f) {
      Dafny.ISequence<Dafny.Rune> _1152_r = (f);
      if ((DCOMP.__default.reserved__fields).Contains(_1152_r)) {
        return Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1152_r, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": r#_")), _1152_r);
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
      var _pat_let_tv134 = dafnyName;
      var _pat_let_tv135 = rs;
      var _pat_let_tv136 = dafnyName;
      if ((new BigInteger((rs).Count)).Sign == 0) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
      } else {
        Std.Wrappers._IOption<DAST._IResolvedType> _1153_res = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
          DAST._IType _source51 = (rs).Select(BigInteger.Zero);
          bool unmatched51 = true;
          if (unmatched51) {
            if (_source51.is_UserDefined) {
              DAST._IResolvedType _1154_resolvedType = _source51.dtor_resolved;
              unmatched51 = false;
              return DCOMP.__default.TraitTypeContainingMethod(_1154_resolvedType, _pat_let_tv134);
            }
          }
          if (unmatched51) {
            DAST._IType _1155___v46 = _source51;
            unmatched51 = false;
            return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
          }
          throw new System.Exception("unexpected control point");
        }))();
        Std.Wrappers._IOption<DAST._IResolvedType> _source52 = _1153_res;
        bool unmatched52 = true;
        if (unmatched52) {
          if (_source52.is_Some) {
            DAST._IResolvedType _1156___v47 = _source52.dtor_value;
            unmatched52 = false;
            return _1153_res;
          }
        }
        if (unmatched52) {
          unmatched52 = false;
          return DCOMP.__default.TraitTypeContainingMethodAux((_pat_let_tv135).Drop(BigInteger.One), _pat_let_tv136);
        }
        throw new System.Exception("unexpected control point");
      }
    }
    public static Std.Wrappers._IOption<DAST._IResolvedType> TraitTypeContainingMethod(DAST._IResolvedType r, Dafny.ISequence<Dafny.Rune> dafnyName)
    {
      DAST._IResolvedType _let_tmp_rhs52 = r;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1157_path = _let_tmp_rhs52.dtor_path;
      Dafny.ISequence<DAST._IType> _1158_typeArgs = _let_tmp_rhs52.dtor_typeArgs;
      DAST._IResolvedTypeBase _1159_kind = _let_tmp_rhs52.dtor_kind;
      Dafny.ISequence<DAST._IAttribute> _1160_attributes = _let_tmp_rhs52.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1161_properMethods = _let_tmp_rhs52.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1162_extendedTypes = _let_tmp_rhs52.dtor_extendedTypes;
      if ((_1161_properMethods).Contains(dafnyName)) {
        return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(r);
      } else {
        return DCOMP.__default.TraitTypeContainingMethodAux(_1162_extendedTypes, dafnyName);
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
      DCOMP._IEnvironment _1163_dt__update__tmp_h0 = this;
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1164_dt__update_htypes_h0 = ((System.Func<Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType>>)(() => {
        var _coll6 = new System.Collections.Generic.List<Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>>();
        foreach (Dafny.ISequence<Dafny.Rune> _compr_6 in ((this).dtor_types).Keys.Elements) {
          Dafny.ISequence<Dafny.Rune> _1165_k = (Dafny.ISequence<Dafny.Rune>)_compr_6;
          if (((this).dtor_types).Contains(_1165_k)) {
            _coll6.Add(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>,RAST._IType>(_1165_k, (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((this).dtor_types,_1165_k)).ToOwned()));
          }
        }
        return Dafny.Map<Dafny.ISequence<Dafny.Rune>,RAST._IType>.FromCollection(_coll6);
      }))();
      return DCOMP.Environment.create((_1163_dt__update__tmp_h0).dtor_names, _1164_dt__update_htypes_h0);
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
      BigInteger _1166_indexInEnv = Std.Collections.Seq.__default.IndexOf<Dafny.ISequence<Dafny.Rune>>((this).dtor_names, name);
      return DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(((this).dtor_names).Subsequence(BigInteger.Zero, _1166_indexInEnv), ((this).dtor_names).Drop((_1166_indexInEnv) + (BigInteger.One))), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Subtract((this).dtor_types, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(name)));
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
      Dafny.ISequence<Dafny.Rune> _1167_modName;
      _1167_modName = DCOMP.__default.escapeName((mod).dtor_name);
      if (((mod).dtor_body).is_None) {
        s = RAST.Mod.create_ExternMod(_1167_modName);
      } else {
        Dafny.ISequence<RAST._IModDecl> _1168_body;
        Dafny.ISequence<RAST._IModDecl> _out15;
        _out15 = (this).GenModuleBody(((mod).dtor_body).dtor_value, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((mod).dtor_name)));
        _1168_body = _out15;
        s = RAST.Mod.create_Mod(_1167_modName, _1168_body);
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenModuleBody(Dafny.ISequence<DAST._IModuleItem> body, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements();
      BigInteger _hi5 = new BigInteger((body).Count);
      for (BigInteger _1169_i = BigInteger.Zero; _1169_i < _hi5; _1169_i++) {
        Dafny.ISequence<RAST._IModDecl> _1170_generated = Dafny.Sequence<RAST._IModDecl>.Empty;
        DAST._IModuleItem _source53 = (body).Select(_1169_i);
        bool unmatched53 = true;
        if (unmatched53) {
          if (_source53.is_Module) {
            DAST._IModule _1171_m = _source53.dtor_Module_a0;
            unmatched53 = false;
            RAST._IMod _1172_mm;
            RAST._IMod _out16;
            _out16 = (this).GenModule(_1171_m, containingPath);
            _1172_mm = _out16;
            _1170_generated = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ModDecl(_1172_mm));
          }
        }
        if (unmatched53) {
          if (_source53.is_Class) {
            DAST._IClass _1173_c = _source53.dtor_Class_a0;
            unmatched53 = false;
            Dafny.ISequence<RAST._IModDecl> _out17;
            _out17 = (this).GenClass(_1173_c, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((_1173_c).dtor_name)));
            _1170_generated = _out17;
          }
        }
        if (unmatched53) {
          if (_source53.is_Trait) {
            DAST._ITrait _1174_t = _source53.dtor_Trait_a0;
            unmatched53 = false;
            Dafny.ISequence<RAST._IModDecl> _out18;
            _out18 = (this).GenTrait(_1174_t, containingPath);
            _1170_generated = _out18;
          }
        }
        if (unmatched53) {
          if (_source53.is_Newtype) {
            DAST._INewtype _1175_n = _source53.dtor_Newtype_a0;
            unmatched53 = false;
            Dafny.ISequence<RAST._IModDecl> _out19;
            _out19 = (this).GenNewtype(_1175_n);
            _1170_generated = _out19;
          }
        }
        if (unmatched53) {
          if (_source53.is_SynonymType) {
            DAST._ISynonymType _1176_s = _source53.dtor_SynonymType_a0;
            unmatched53 = false;
            Dafny.ISequence<RAST._IModDecl> _out20;
            _out20 = (this).GenSynonymType(_1176_s);
            _1170_generated = _out20;
          }
        }
        if (unmatched53) {
          DAST._IDatatype _1177_d = _source53.dtor_Datatype_a0;
          unmatched53 = false;
          Dafny.ISequence<RAST._IModDecl> _out21;
          _out21 = (this).GenDatatype(_1177_d);
          _1170_generated = _out21;
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, _1170_generated);
      }
      return s;
    }
    public void GenTypeParam(DAST._ITypeArgDecl tp, out DAST._IType typeArg, out RAST._ITypeParamDecl typeParam)
    {
      typeArg = DAST.Type.Default();
      typeParam = RAST.TypeParamDecl.Default();
      typeArg = DAST.Type.create_TypeArg((tp).dtor_name);
      Dafny.ISequence<RAST._IType> _1178_genTpConstraint;
      _1178_genTpConstraint = ((((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsEquality())) ? (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyTypeEq)) : (Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DafnyType)));
      if (((tp).dtor_bounds).Contains(DAST.TypeArgBound.create_SupportsDefault())) {
        _1178_genTpConstraint = Dafny.Sequence<RAST._IType>.Concat(_1178_genTpConstraint, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default"))));
      }
      typeParam = RAST.TypeParamDecl.create(DCOMP.__default.escapeName(((tp).dtor_name)), _1178_genTpConstraint);
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
        for (BigInteger _1179_tpI = BigInteger.Zero; _1179_tpI < _hi6; _1179_tpI++) {
          DAST._ITypeArgDecl _1180_tp;
          _1180_tp = (@params).Select(_1179_tpI);
          DAST._IType _1181_typeArg;
          RAST._ITypeParamDecl _1182_typeParam;
          DAST._IType _out22;
          RAST._ITypeParamDecl _out23;
          (this).GenTypeParam(_1180_tp, out _out22, out _out23);
          _1181_typeArg = _out22;
          _1182_typeParam = _out23;
          RAST._IType _1183_rType;
          RAST._IType _out24;
          _out24 = (this).GenType(_1181_typeArg, DCOMP.GenTypeContext.@default());
          _1183_rType = _out24;
          typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1181_typeArg));
          typeParams = Dafny.Sequence<RAST._IType>.Concat(typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1183_rType));
          constrainedTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(constrainedTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1182_typeParam));
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
      Dafny.ISequence<DAST._IType> _1184_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1185_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1186_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1187_whereConstraints;
      Dafny.ISequence<DAST._IType> _out25;
      Dafny.ISequence<RAST._IType> _out26;
      Dafny.ISequence<RAST._ITypeParamDecl> _out27;
      Dafny.ISequence<Dafny.Rune> _out28;
      (this).GenTypeParameters((c).dtor_typeParams, out _out25, out _out26, out _out27, out _out28);
      _1184_typeParamsSeq = _out25;
      _1185_rTypeParams = _out26;
      _1186_rTypeParamsDecls = _out27;
      _1187_whereConstraints = _out28;
      Dafny.ISequence<Dafny.Rune> _1188_constrainedTypeParams;
      _1188_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1186_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<RAST._IField> _1189_fields;
      _1189_fields = Dafny.Sequence<RAST._IField>.FromElements();
      Dafny.ISequence<RAST._IAssignIdentifier> _1190_fieldInits;
      _1190_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
      BigInteger _hi7 = new BigInteger(((c).dtor_fields).Count);
      for (BigInteger _1191_fieldI = BigInteger.Zero; _1191_fieldI < _hi7; _1191_fieldI++) {
        DAST._IField _1192_field;
        _1192_field = ((c).dtor_fields).Select(_1191_fieldI);
        RAST._IType _1193_fieldType;
        RAST._IType _out29;
        _out29 = (this).GenType(((_1192_field).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
        _1193_fieldType = _out29;
        Dafny.ISequence<Dafny.Rune> _1194_fieldRustName;
        _1194_fieldRustName = DCOMP.__default.escapeName(((_1192_field).dtor_formal).dtor_name);
        _1189_fields = Dafny.Sequence<RAST._IField>.Concat(_1189_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PUB(), RAST.Formal.create(_1194_fieldRustName, _1193_fieldType))));
        Std.Wrappers._IOption<DAST._IExpression> _source54 = (_1192_field).dtor_defaultValue;
        bool unmatched54 = true;
        if (unmatched54) {
          if (_source54.is_Some) {
            DAST._IExpression _1195_e = _source54.dtor_value;
            unmatched54 = false;
            {
              RAST._IExpr _1196_expr;
              DCOMP._IOwnership _1197___v48;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1198___v49;
              RAST._IExpr _out30;
              DCOMP._IOwnership _out31;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out32;
              (this).GenExpr(_1195_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out30, out _out31, out _out32);
              _1196_expr = _out30;
              _1197___v48 = _out31;
              _1198___v49 = _out32;
              _1190_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1190_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1194_fieldRustName, _1196_expr)));
            }
          }
        }
        if (unmatched54) {
          unmatched54 = false;
          {
            RAST._IExpr _1199_default;
            _1199_default = RAST.__default.std__Default__default;
            if ((_1193_fieldType).IsObjectOrPointer()) {
              _1199_default = (_1193_fieldType).ToNullExpr();
            }
            _1190_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1190_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1194_fieldRustName, _1199_default)));
          }
        }
      }
      BigInteger _hi8 = new BigInteger(((c).dtor_typeParams).Count);
      for (BigInteger _1200_typeParamI = BigInteger.Zero; _1200_typeParamI < _hi8; _1200_typeParamI++) {
        DAST._IType _1201_typeArg;
        RAST._ITypeParamDecl _1202_typeParam;
        DAST._IType _out33;
        RAST._ITypeParamDecl _out34;
        (this).GenTypeParam(((c).dtor_typeParams).Select(_1200_typeParamI), out _out33, out _out34);
        _1201_typeArg = _out33;
        _1202_typeParam = _out34;
        RAST._IType _1203_rTypeArg;
        RAST._IType _out35;
        _out35 = (this).GenType(_1201_typeArg, DCOMP.GenTypeContext.@default());
        _1203_rTypeArg = _out35;
        _1189_fields = Dafny.Sequence<RAST._IField>.Concat(_1189_fields, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1200_typeParamI)), RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1203_rTypeArg))))));
        _1190_fieldInits = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1190_fieldInits, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_phantom_type_param_"), Std.Strings.__default.OfNat(_1200_typeParamI)), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::marker::PhantomData")))));
      }
      Dafny.ISequence<Dafny.Rune> _1204_datatypeName;
      _1204_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IStruct _1205_struct;
      _1205_struct = RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1204_datatypeName, _1186_rTypeParamsDecls, RAST.Fields.create_NamedFields(_1189_fields));
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(_1205_struct));
      Dafny.ISequence<RAST._IImplMember> _1206_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1207_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out36;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out37;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(path, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Class(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1184_typeParamsSeq, out _out36, out _out37);
      _1206_implBodyRaw = _out36;
      _1207_traitBodies = _out37;
      Dafny.ISequence<RAST._IImplMember> _1208_implBody;
      _1208_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create((this).allocate__fn, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some((this).Object(RAST.Type.create_SelfOwned())), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel((this).allocate)).ApplyType1(RAST.Type.create_SelfOwned())).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()))))), _1206_implBodyRaw);
      RAST._IImpl _1209_i;
      _1209_i = RAST.Impl.create_Impl(_1186_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1204_datatypeName), _1185_rTypeParams), _1187_whereConstraints, _1208_implBody);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(_1209_i)));
      RAST._IType _1210_genSelfPath;
      RAST._IType _out38;
      _out38 = DCOMP.COMP.GenPath(path);
      _1210_genSelfPath = _out38;
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1186_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"))))), RAST.Type.create_TypeApp(_1210_genSelfPath, _1185_rTypeParams), _1187_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any")))))))))));
      BigInteger _hi9 = new BigInteger(((c).dtor_superClasses).Count);
      for (BigInteger _1211_i = BigInteger.Zero; _1211_i < _hi9; _1211_i++) {
        DAST._IType _1212_superClass;
        _1212_superClass = ((c).dtor_superClasses).Select(_1211_i);
        DAST._IType _source55 = _1212_superClass;
        bool unmatched55 = true;
        if (unmatched55) {
          if (_source55.is_UserDefined) {
            DAST._IResolvedType resolved0 = _source55.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1213_traitPath = resolved0.dtor_path;
            Dafny.ISequence<DAST._IType> _1214_typeArgs = resolved0.dtor_typeArgs;
            DAST._IResolvedTypeBase kind0 = resolved0.dtor_kind;
            if (kind0.is_Trait) {
              Dafny.ISequence<DAST._IAttribute> _1215___v50 = resolved0.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1216___v51 = resolved0.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1217___v52 = resolved0.dtor_extendedTypes;
              unmatched55 = false;
              {
                RAST._IType _1218_pathStr;
                RAST._IType _out39;
                _out39 = DCOMP.COMP.GenPath(_1213_traitPath);
                _1218_pathStr = _out39;
                Dafny.ISequence<RAST._IType> _1219_typeArgs;
                Dafny.ISequence<RAST._IType> _out40;
                _out40 = (this).GenTypeArgs(_1214_typeArgs, DCOMP.GenTypeContext.@default());
                _1219_typeArgs = _out40;
                Dafny.ISequence<RAST._IImplMember> _1220_body;
                _1220_body = Dafny.Sequence<RAST._IImplMember>.FromElements();
                if ((_1207_traitBodies).Contains(_1213_traitPath)) {
                  _1220_body = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(_1207_traitBodies,_1213_traitPath);
                }
                RAST._IType _1221_traitType;
                _1221_traitType = RAST.Type.create_TypeApp(_1218_pathStr, _1219_typeArgs);
                RAST._IModDecl _1222_x;
                _1222_x = RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1186_rTypeParamsDecls, _1221_traitType, RAST.Type.create_TypeApp(_1210_genSelfPath, _1185_rTypeParams), _1187_whereConstraints, _1220_body));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(_1222_x));
                s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1186_rTypeParamsDecls, ((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_DynType(_1221_traitType))), RAST.Type.create_TypeApp(_1210_genSelfPath, _1185_rTypeParams), _1187_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_ImplMemberMacro(((RAST.__default.dafny__runtime).MSel((this).UpcastFnMacro)).Apply1(RAST.Expr.create_ExprFromType(RAST.Type.create_DynType(_1221_traitType)))))))));
              }
            }
          }
        }
        if (unmatched55) {
          DAST._IType _1223___v53 = _source55;
          unmatched55 = false;
        }
      }
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenTrait(DAST._ITrait t, Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> containingPath)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1224_typeParamsSeq;
      _1224_typeParamsSeq = Dafny.Sequence<DAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1225_typeParamDecls;
      _1225_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IType> _1226_typeParams;
      _1226_typeParams = Dafny.Sequence<RAST._IType>.FromElements();
      if ((new BigInteger(((t).dtor_typeParams).Count)).Sign == 1) {
        BigInteger _hi10 = new BigInteger(((t).dtor_typeParams).Count);
        for (BigInteger _1227_tpI = BigInteger.Zero; _1227_tpI < _hi10; _1227_tpI++) {
          DAST._ITypeArgDecl _1228_tp;
          _1228_tp = ((t).dtor_typeParams).Select(_1227_tpI);
          DAST._IType _1229_typeArg;
          RAST._ITypeParamDecl _1230_typeParamDecl;
          DAST._IType _out41;
          RAST._ITypeParamDecl _out42;
          (this).GenTypeParam(_1228_tp, out _out41, out _out42);
          _1229_typeArg = _out41;
          _1230_typeParamDecl = _out42;
          _1224_typeParamsSeq = Dafny.Sequence<DAST._IType>.Concat(_1224_typeParamsSeq, Dafny.Sequence<DAST._IType>.FromElements(_1229_typeArg));
          _1225_typeParamDecls = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1225_typeParamDecls, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1230_typeParamDecl));
          RAST._IType _1231_typeParam;
          RAST._IType _out43;
          _out43 = (this).GenType(_1229_typeArg, DCOMP.GenTypeContext.@default());
          _1231_typeParam = _out43;
          _1226_typeParams = Dafny.Sequence<RAST._IType>.Concat(_1226_typeParams, Dafny.Sequence<RAST._IType>.FromElements(_1231_typeParam));
        }
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1232_fullPath;
      _1232_fullPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(containingPath, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((t).dtor_name));
      Dafny.ISequence<RAST._IImplMember> _1233_implBody;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1234___v54;
      Dafny.ISequence<RAST._IImplMember> _out44;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out45;
      (this).GenClassImplBody((t).dtor_body, true, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1232_fullPath, Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Trait(), (t).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1224_typeParamsSeq, out _out44, out _out45);
      _1233_implBody = _out44;
      _1234___v54 = _out45;
      Dafny.ISequence<RAST._IType> _1235_parents;
      _1235_parents = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi11 = new BigInteger(((t).dtor_parents).Count);
      for (BigInteger _1236_i = BigInteger.Zero; _1236_i < _hi11; _1236_i++) {
        RAST._IType _1237_tpe;
        RAST._IType _out46;
        _out46 = (this).GenType(((t).dtor_parents).Select(_1236_i), DCOMP.GenTypeContext.ForTraitParents());
        _1237_tpe = _out46;
        _1235_parents = Dafny.Sequence<RAST._IType>.Concat(Dafny.Sequence<RAST._IType>.Concat(_1235_parents, Dafny.Sequence<RAST._IType>.FromElements(_1237_tpe)), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.dafny__runtime__type).MSel((this).Upcast)).Apply1(RAST.Type.create_DynType(_1237_tpe))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TraitDecl(RAST.Trait.create(_1225_typeParamDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(DCOMP.__default.escapeName((t).dtor_name)), _1226_typeParams), _1235_parents, _1233_implBody)));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenNewtype(DAST._INewtype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1238_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1239_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1240_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1241_whereConstraints;
      Dafny.ISequence<DAST._IType> _out47;
      Dafny.ISequence<RAST._IType> _out48;
      Dafny.ISequence<RAST._ITypeParamDecl> _out49;
      Dafny.ISequence<Dafny.Rune> _out50;
      (this).GenTypeParameters((c).dtor_typeParams, out _out47, out _out48, out _out49, out _out50);
      _1238_typeParamsSeq = _out47;
      _1239_rTypeParams = _out48;
      _1240_rTypeParamsDecls = _out49;
      _1241_whereConstraints = _out50;
      Dafny.ISequence<Dafny.Rune> _1242_constrainedTypeParams;
      _1242_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1240_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      RAST._IType _1243_underlyingType = RAST.Type.Default();
      Std.Wrappers._IOption<RAST._IType> _source56 = DCOMP.COMP.NewtypeToRustType((c).dtor_base, (c).dtor_range);
      bool unmatched56 = true;
      if (unmatched56) {
        if (_source56.is_Some) {
          RAST._IType _1244_v = _source56.dtor_value;
          unmatched56 = false;
          _1243_underlyingType = _1244_v;
        }
      }
      if (unmatched56) {
        unmatched56 = false;
        RAST._IType _out51;
        _out51 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
        _1243_underlyingType = _out51;
      }
      DAST._IType _1245_resultingType;
      _1245_resultingType = DAST.Type.create_UserDefined(DAST.ResolvedType.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements(), DAST.ResolvedTypeBase.create_Newtype((c).dtor_base, (c).dtor_range, false), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements()));
      Dafny.ISequence<Dafny.Rune> _1246_newtypeName;
      _1246_newtypeName = DCOMP.__default.escapeName((c).dtor_name);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_StructDecl(RAST.Struct.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone, PartialEq)]"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[repr(transparent)]")), _1246_newtypeName, _1240_rTypeParamsDecls, RAST.Fields.create_NamelessFields(Dafny.Sequence<RAST._INamelessField>.FromElements(RAST.NamelessField.create(RAST.Visibility.create_PUB(), _1243_underlyingType))))));
      RAST._IExpr _1247_fnBody;
      _1247_fnBody = RAST.Expr.create_Identifier(_1246_newtypeName);
      Std.Wrappers._IOption<DAST._IExpression> _source57 = (c).dtor_witnessExpr;
      bool unmatched57 = true;
      if (unmatched57) {
        if (_source57.is_Some) {
          DAST._IExpression _1248_e = _source57.dtor_value;
          unmatched57 = false;
          {
            DAST._IExpression _1249_e;
            _1249_e = ((object.Equals((c).dtor_base, _1245_resultingType)) ? (_1248_e) : (DAST.Expression.create_Convert(_1248_e, (c).dtor_base, _1245_resultingType)));
            RAST._IExpr _1250_eStr;
            DCOMP._IOwnership _1251___v55;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1252___v56;
            RAST._IExpr _out52;
            DCOMP._IOwnership _out53;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out54;
            (this).GenExpr(_1249_e, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out52, out _out53, out _out54);
            _1250_eStr = _out52;
            _1251___v55 = _out53;
            _1252___v56 = _out54;
            _1247_fnBody = (_1247_fnBody).Apply1(_1250_eStr);
          }
        }
      }
      if (unmatched57) {
        unmatched57 = false;
        {
          _1247_fnBody = (_1247_fnBody).Apply1(RAST.__default.std__Default__default);
        }
      }
      RAST._IImplMember _1253_body;
      _1253_body = RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1247_fnBody)));
      Std.Wrappers._IOption<DAST._INewtypeConstraint> _source58 = (c).dtor_constraint;
      bool unmatched58 = true;
      if (unmatched58) {
        if (_source58.is_None) {
          unmatched58 = false;
        }
      }
      if (unmatched58) {
        DAST._INewtypeConstraint value8 = _source58.dtor_value;
        DAST._IFormal _1254_formal = value8.dtor_variable;
        Dafny.ISequence<DAST._IStatement> _1255_constraintStmts = value8.dtor_constraintStmts;
        unmatched58 = false;
        RAST._IExpr _1256_rStmts;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1257___v57;
        DCOMP._IEnvironment _1258_newEnv;
        RAST._IExpr _out55;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out56;
        DCOMP._IEnvironment _out57;
        (this).GenStmts(_1255_constraintStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out55, out _out56, out _out57);
        _1256_rStmts = _out55;
        _1257___v57 = _out56;
        _1258_newEnv = _out57;
        Dafny.ISequence<RAST._IFormal> _1259_rFormals;
        Dafny.ISequence<RAST._IFormal> _out58;
        _out58 = (this).GenParams(Dafny.Sequence<DAST._IFormal>.FromElements(_1254_formal));
        _1259_rFormals = _out58;
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1240_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1246_newtypeName), _1239_rTypeParams), _1241_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("is"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), _1259_rFormals, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1256_rStmts))))))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1240_rTypeParamsDecls, RAST.__default.DefaultTrait, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1246_newtypeName), _1239_rTypeParams), _1241_whereConstraints, Dafny.Sequence<RAST._IImplMember>.FromElements(_1253_body)))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1240_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1246_newtypeName), _1239_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&mut ::std::fmt::Formatter"))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))))))))));
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1240_rTypeParamsDecls, RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1246_newtypeName), _1239_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_RawImplMember(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("type Target = "), (_1243_underlyingType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";"))), RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("deref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some((RAST.__default.SelfBorrowed).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Target"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&self.0"))))))))));
      return s;
    }
    public Dafny.ISequence<RAST._IModDecl> GenSynonymType(DAST._ISynonymType c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1260_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1261_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1262_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1263_whereConstraints;
      Dafny.ISequence<DAST._IType> _out59;
      Dafny.ISequence<RAST._IType> _out60;
      Dafny.ISequence<RAST._ITypeParamDecl> _out61;
      Dafny.ISequence<Dafny.Rune> _out62;
      (this).GenTypeParameters((c).dtor_typeParams, out _out59, out _out60, out _out61, out _out62);
      _1260_typeParamsSeq = _out59;
      _1261_rTypeParams = _out60;
      _1262_rTypeParamsDecls = _out61;
      _1263_whereConstraints = _out62;
      Dafny.ISequence<Dafny.Rune> _1264_constrainedTypeParams;
      _1264_constrainedTypeParams = RAST.TypeParamDecl.ToStringMultiple(_1262_rTypeParamsDecls, Dafny.Sequence<Dafny.Rune>.Concat(RAST.__default.IND, RAST.__default.IND));
      Dafny.ISequence<Dafny.Rune> _1265_synonymTypeName;
      _1265_synonymTypeName = DCOMP.__default.escapeName((c).dtor_name);
      RAST._IType _1266_resultingType;
      RAST._IType _out63;
      _out63 = (this).GenType((c).dtor_base, DCOMP.GenTypeContext.@default());
      _1266_resultingType = _out63;
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TypeDecl(RAST.TypeSynonym.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), _1265_synonymTypeName, _1262_rTypeParamsDecls, _1266_resultingType)));
      Std.Wrappers._IOption<DAST._IExpression> _source59 = (c).dtor_witnessExpr;
      bool unmatched59 = true;
      if (unmatched59) {
        if (_source59.is_Some) {
          DAST._IExpression _1267_e = _source59.dtor_value;
          unmatched59 = false;
          {
            RAST._IExpr _1268_rStmts;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1269___v58;
            DCOMP._IEnvironment _1270_newEnv;
            RAST._IExpr _out64;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out65;
            DCOMP._IEnvironment _out66;
            (this).GenStmts((c).dtor_witnessStmts, DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.Empty(), false, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out64, out _out65, out _out66);
            _1268_rStmts = _out64;
            _1269___v58 = _out65;
            _1270_newEnv = _out66;
            RAST._IExpr _1271_rExpr;
            DCOMP._IOwnership _1272___v59;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1273___v60;
            RAST._IExpr _out67;
            DCOMP._IOwnership _out68;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out69;
            (this).GenExpr(_1267_e, DCOMP.SelfInfo.create_NoSelf(), _1270_newEnv, DCOMP.Ownership.create_OwnershipOwned(), out _out67, out _out68, out _out69);
            _1271_rExpr = _out67;
            _1272___v59 = _out68;
            _1273___v60 = _out69;
            Dafny.ISequence<Dafny.Rune> _1274_constantName;
            _1274_constantName = DCOMP.__default.escapeName(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_init_"), ((c).dtor_name)));
            s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_TopFnDecl(RAST.TopFnDecl.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), RAST.Visibility.create_PUB(), RAST.Fn.create(_1274_constantName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1266_resultingType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((_1268_rStmts).Then(_1271_rExpr)))))));
          }
        }
      }
      if (unmatched59) {
        unmatched59 = false;
      }
      return s;
    }
    public bool TypeIsEq(DAST._IType t) {
      DAST._IType _source60 = t;
      bool unmatched60 = true;
      if (unmatched60) {
        if (_source60.is_UserDefined) {
          DAST._IResolvedType _1275___v61 = _source60.dtor_resolved;
          unmatched60 = false;
          return true;
        }
      }
      if (unmatched60) {
        if (_source60.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1276_ts = _source60.dtor_Tuple_a0;
          unmatched60 = false;
          return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IType>, bool>>((_1277_ts) => Dafny.Helpers.Quantifier<DAST._IType>((_1277_ts).UniqueElements, true, (((_forall_var_5) => {
            DAST._IType _1278_t = (DAST._IType)_forall_var_5;
            return !((_1277_ts).Contains(_1278_t)) || ((this).TypeIsEq(_1278_t));
          }))))(_1276_ts);
        }
      }
      if (unmatched60) {
        if (_source60.is_Array) {
          DAST._IType _1279_t = _source60.dtor_element;
          BigInteger _1280___v62 = _source60.dtor_dims;
          unmatched60 = false;
          return (this).TypeIsEq(_1279_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_Seq) {
          DAST._IType _1281_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1281_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_Set) {
          DAST._IType _1282_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1282_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_Multiset) {
          DAST._IType _1283_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1283_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_Map) {
          DAST._IType _1284_k = _source60.dtor_key;
          DAST._IType _1285_v = _source60.dtor_value;
          unmatched60 = false;
          return ((this).TypeIsEq(_1284_k)) && ((this).TypeIsEq(_1285_v));
        }
      }
      if (unmatched60) {
        if (_source60.is_SetBuilder) {
          DAST._IType _1286_t = _source60.dtor_element;
          unmatched60 = false;
          return (this).TypeIsEq(_1286_t);
        }
      }
      if (unmatched60) {
        if (_source60.is_MapBuilder) {
          DAST._IType _1287_k = _source60.dtor_key;
          DAST._IType _1288_v = _source60.dtor_value;
          unmatched60 = false;
          return ((this).TypeIsEq(_1287_k)) && ((this).TypeIsEq(_1288_v));
        }
      }
      if (unmatched60) {
        if (_source60.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1289___v63 = _source60.dtor_args;
          DAST._IType _1290___v64 = _source60.dtor_result;
          unmatched60 = false;
          return false;
        }
      }
      if (unmatched60) {
        if (_source60.is_Primitive) {
          DAST._IPrimitive _1291___v65 = _source60.dtor_Primitive_a0;
          unmatched60 = false;
          return true;
        }
      }
      if (unmatched60) {
        if (_source60.is_Passthrough) {
          Dafny.ISequence<Dafny.Rune> _1292___v66 = _source60.dtor_Passthrough_a0;
          unmatched60 = false;
          return true;
        }
      }
      if (unmatched60) {
        if (_source60.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _1293_i = _source60.dtor_TypeArg_a0;
          unmatched60 = false;
          return true;
        }
      }
      if (unmatched60) {
        unmatched60 = false;
        return true;
      }
      throw new System.Exception("unexpected control point");
    }
    public bool DatatypeIsEq(DAST._IDatatype c) {
      return (!((c).dtor_isCo)) && (Dafny.Helpers.Id<Func<DAST._IDatatype, bool>>((_1294_c) => Dafny.Helpers.Quantifier<DAST._IDatatypeCtor>(((_1294_c).dtor_ctors).UniqueElements, true, (((_forall_var_6) => {
        DAST._IDatatypeCtor _1295_ctor = (DAST._IDatatypeCtor)_forall_var_6;
        return Dafny.Helpers.Quantifier<DAST._IDatatypeDtor>(((_1295_ctor).dtor_args).UniqueElements, true, (((_forall_var_7) => {
          DAST._IDatatypeDtor _1296_arg = (DAST._IDatatypeDtor)_forall_var_7;
          return !((((_1294_c).dtor_ctors).Contains(_1295_ctor)) && (((_1295_ctor).dtor_args).Contains(_1296_arg))) || ((this).TypeIsEq(((_1296_arg).dtor_formal).dtor_typ));
        })));
      }))))(c));
    }
    public Dafny.ISequence<RAST._IModDecl> GenDatatype(DAST._IDatatype c)
    {
      Dafny.ISequence<RAST._IModDecl> s = Dafny.Sequence<RAST._IModDecl>.Empty;
      Dafny.ISequence<DAST._IType> _1297_typeParamsSeq;
      Dafny.ISequence<RAST._IType> _1298_rTypeParams;
      Dafny.ISequence<RAST._ITypeParamDecl> _1299_rTypeParamsDecls;
      Dafny.ISequence<Dafny.Rune> _1300_whereConstraints;
      Dafny.ISequence<DAST._IType> _out70;
      Dafny.ISequence<RAST._IType> _out71;
      Dafny.ISequence<RAST._ITypeParamDecl> _out72;
      Dafny.ISequence<Dafny.Rune> _out73;
      (this).GenTypeParameters((c).dtor_typeParams, out _out70, out _out71, out _out72, out _out73);
      _1297_typeParamsSeq = _out70;
      _1298_rTypeParams = _out71;
      _1299_rTypeParamsDecls = _out72;
      _1300_whereConstraints = _out73;
      Dafny.ISequence<Dafny.Rune> _1301_datatypeName;
      _1301_datatypeName = DCOMP.__default.escapeName((c).dtor_name);
      Dafny.ISequence<RAST._IEnumCase> _1302_ctors;
      _1302_ctors = Dafny.Sequence<RAST._IEnumCase>.FromElements();
      Dafny.ISequence<DAST._IVariance> _1303_variances;
      _1303_variances = Std.Collections.Seq.__default.Map<DAST._ITypeArgDecl, DAST._IVariance>(((System.Func<DAST._ITypeArgDecl, DAST._IVariance>)((_1304_typeParamDecl) => {
        return (_1304_typeParamDecl).dtor_variance;
      })), (c).dtor_typeParams);
      BigInteger _hi12 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1305_i = BigInteger.Zero; _1305_i < _hi12; _1305_i++) {
        DAST._IDatatypeCtor _1306_ctor;
        _1306_ctor = ((c).dtor_ctors).Select(_1305_i);
        Dafny.ISequence<RAST._IField> _1307_ctorArgs;
        _1307_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1308_isNumeric;
        _1308_isNumeric = false;
        BigInteger _hi13 = new BigInteger(((_1306_ctor).dtor_args).Count);
        for (BigInteger _1309_j = BigInteger.Zero; _1309_j < _hi13; _1309_j++) {
          DAST._IDatatypeDtor _1310_dtor;
          _1310_dtor = ((_1306_ctor).dtor_args).Select(_1309_j);
          RAST._IType _1311_formalType;
          RAST._IType _out74;
          _out74 = (this).GenType(((_1310_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1311_formalType = _out74;
          Dafny.ISequence<Dafny.Rune> _1312_formalName;
          _1312_formalName = DCOMP.__default.escapeName(((_1310_dtor).dtor_formal).dtor_name);
          if (((_1309_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1312_formalName))) {
            _1308_isNumeric = true;
          }
          if ((((_1309_j).Sign != 0) && (_1308_isNumeric)) && (!(Std.Strings.__default.OfNat(_1309_j)).Equals(_1312_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1312_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1309_j)));
            _1308_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1307_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1307_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1312_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1311_formalType))))));
          } else {
            _1307_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1307_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1312_formalName, _1311_formalType))));
          }
        }
        RAST._IFields _1313_namedFields;
        _1313_namedFields = RAST.Fields.create_NamedFields(_1307_ctorArgs);
        if (_1308_isNumeric) {
          _1313_namedFields = (_1313_namedFields).ToNamelessFields();
        }
        _1302_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1302_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1306_ctor).dtor_name), _1313_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1314_selfPath;
      _1314_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1315_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1316_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out75;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out76;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1314_selfPath, _1297_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(_1303_variances), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1297_typeParamsSeq, out _out75, out _out76);
      _1315_implBodyRaw = _out75;
      _1316_traitBodies = _out76;
      Dafny.ISequence<RAST._IImplMember> _1317_implBody;
      _1317_implBody = _1315_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1318_emittedFields;
      _1318_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi14 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1319_i = BigInteger.Zero; _1319_i < _hi14; _1319_i++) {
        DAST._IDatatypeCtor _1320_ctor;
        _1320_ctor = ((c).dtor_ctors).Select(_1319_i);
        BigInteger _hi15 = new BigInteger(((_1320_ctor).dtor_args).Count);
        for (BigInteger _1321_j = BigInteger.Zero; _1321_j < _hi15; _1321_j++) {
          DAST._IDatatypeDtor _1322_dtor;
          _1322_dtor = ((_1320_ctor).dtor_args).Select(_1321_j);
          Dafny.ISequence<Dafny.Rune> _1323_callName;
          _1323_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1322_dtor).dtor_callName, DCOMP.__default.escapeName(((_1322_dtor).dtor_formal).dtor_name));
          if (!((_1318_emittedFields).Contains(_1323_callName))) {
            _1318_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1318_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1323_callName));
            RAST._IType _1324_formalType;
            RAST._IType _out77;
            _out77 = (this).GenType(((_1322_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1324_formalType = _out77;
            Dafny.ISequence<RAST._IMatchCase> _1325_cases;
            _1325_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1326_k = BigInteger.Zero; _1326_k < _hi16; _1326_k++) {
              DAST._IDatatypeCtor _1327_ctor2;
              _1327_ctor2 = ((c).dtor_ctors).Select(_1326_k);
              Dafny.ISequence<Dafny.Rune> _1328_pattern;
              _1328_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1301_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1327_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1329_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1330_hasMatchingField;
              _1330_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1331_patternInner;
              _1331_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1332_isNumeric;
              _1332_isNumeric = false;
              BigInteger _hi17 = new BigInteger(((_1327_ctor2).dtor_args).Count);
              for (BigInteger _1333_l = BigInteger.Zero; _1333_l < _hi17; _1333_l++) {
                DAST._IDatatypeDtor _1334_dtor2;
                _1334_dtor2 = ((_1327_ctor2).dtor_args).Select(_1333_l);
                Dafny.ISequence<Dafny.Rune> _1335_patternName;
                _1335_patternName = DCOMP.__default.escapeDtor(((_1334_dtor2).dtor_formal).dtor_name);
                if (((_1333_l).Sign == 0) && ((_1335_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1332_isNumeric = true;
                }
                if (_1332_isNumeric) {
                  _1335_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1334_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1333_l)));
                }
                if (object.Equals(((_1322_dtor).dtor_formal).dtor_name, ((_1334_dtor2).dtor_formal).dtor_name)) {
                  _1330_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1335_patternName);
                }
                _1331_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1331_patternInner, _1335_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1332_isNumeric) {
                _1328_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1328_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1331_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1328_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1328_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1331_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1330_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1329_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1330_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1329_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1330_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1329_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1336_ctorMatch;
              _1336_ctorMatch = RAST.MatchCase.create(_1328_pattern, RAST.Expr.create_RawExpr(_1329_rhs));
              _1325_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1325_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1336_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1325_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1325_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1301_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1337_methodBody;
            _1337_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1325_cases);
            _1317_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1317_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1323_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1324_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1337_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1338_coerceTypes;
      _1338_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1339_rCoerceTypeParams;
      _1339_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1340_coerceArguments;
      _1340_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1341_coerceMap;
      _1341_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1342_rCoerceMap;
      _1342_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1343_coerceMapToArg;
      _1343_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1344_types;
        _1344_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi18 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1345_typeI = BigInteger.Zero; _1345_typeI < _hi18; _1345_typeI++) {
          DAST._ITypeArgDecl _1346_typeParam;
          _1346_typeParam = ((c).dtor_typeParams).Select(_1345_typeI);
          DAST._IType _1347_typeArg;
          RAST._ITypeParamDecl _1348_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(_1346_typeParam, out _out78, out _out79);
          _1347_typeArg = _out78;
          _1348_rTypeParamDecl = _out79;
          RAST._IType _1349_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1347_typeArg, DCOMP.GenTypeContext.@default());
          _1349_rTypeArg = _out80;
          _1344_types = Dafny.Sequence<RAST._IType>.Concat(_1344_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1349_rTypeArg))));
          if (((_1345_typeI) < (new BigInteger((_1303_variances).Count))) && (((_1303_variances).Select(_1345_typeI)).is_Nonvariant)) {
            _1338_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1338_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1349_rTypeArg));
            goto continue0;
          }
          DAST._ITypeArgDecl _1350_coerceTypeParam;
          _1350_coerceTypeParam = Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_1346_typeParam, _pat_let9_0 => Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_pat_let9_0, _1351_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1345_typeI)), _pat_let10_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(_pat_let10_0, _1352_dt__update_hname_h0 => DAST.TypeArgDecl.create(_1352_dt__update_hname_h0, (_1351_dt__update__tmp_h0).dtor_bounds, (_1351_dt__update__tmp_h0).dtor_variance)))));
          DAST._IType _1353_coerceTypeArg;
          RAST._ITypeParamDecl _1354_rCoerceTypeParamDecl;
          DAST._IType _out81;
          RAST._ITypeParamDecl _out82;
          (this).GenTypeParam(_1350_coerceTypeParam, out _out81, out _out82);
          _1353_coerceTypeArg = _out81;
          _1354_rCoerceTypeParamDecl = _out82;
          _1341_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1341_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1347_typeArg, _1353_coerceTypeArg)));
          RAST._IType _1355_rCoerceType;
          RAST._IType _out83;
          _out83 = (this).GenType(_1353_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1355_rCoerceType = _out83;
          _1342_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1342_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1349_rTypeArg, _1355_rCoerceType)));
          _1338_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1338_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1355_rCoerceType));
          _1339_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1339_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1354_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1356_coerceFormal;
          _1356_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1345_typeI));
          _1343_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1343_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1349_rTypeArg, _1355_rCoerceType), (RAST.Expr.create_Identifier(_1356_coerceFormal)).Clone())));
          _1340_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1340_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1356_coerceFormal, RAST.__default.Rc(RAST.Type.create_IntersectionType(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1349_rTypeArg), _1355_rCoerceType)), RAST.__default.StaticTrait)))));
        continue0: ;
        }
      after0: ;
        _1302_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1302_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1357_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1357_tpe);
})), _1344_types)))));
      }
      bool _1358_cIsEq;
      _1358_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1358_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1301_datatypeName, _1299_rTypeParamsDecls, _1302_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1299_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams), _1300_whereConstraints, _1317_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1359_printImplBodyCases;
      _1359_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1360_hashImplBodyCases;
      _1360_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1361_coerceImplBodyCases;
      _1361_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi19 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1362_i = BigInteger.Zero; _1362_i < _hi19; _1362_i++) {
        DAST._IDatatypeCtor _1363_ctor;
        _1363_ctor = ((c).dtor_ctors).Select(_1362_i);
        Dafny.ISequence<Dafny.Rune> _1364_ctorMatch;
        _1364_ctorMatch = DCOMP.__default.escapeName((_1363_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1365_modulePrefix;
        _1365_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1366_ctorName;
        _1366_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1365_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1363_ctor).dtor_name));
        if (((new BigInteger((_1366_ctorName).Count)) >= (new BigInteger(13))) && (((_1366_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1366_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1367_printRhs;
        _1367_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1366_ctorName), (((_1363_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1368_hashRhs;
        _1368_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1369_coerceRhsArgs;
        _1369_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1370_isNumeric;
        _1370_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1371_ctorMatchInner;
        _1371_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi20 = new BigInteger(((_1363_ctor).dtor_args).Count);
        for (BigInteger _1372_j = BigInteger.Zero; _1372_j < _hi20; _1372_j++) {
          DAST._IDatatypeDtor _1373_dtor;
          _1373_dtor = ((_1363_ctor).dtor_args).Select(_1372_j);
          Dafny.ISequence<Dafny.Rune> _1374_patternName;
          _1374_patternName = DCOMP.__default.escapeField(((_1373_dtor).dtor_formal).dtor_name);
          DAST._IType _1375_formalType;
          _1375_formalType = ((_1373_dtor).dtor_formal).dtor_typ;
          if (((_1372_j).Sign == 0) && ((_1374_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1370_isNumeric = true;
          }
          if (_1370_isNumeric) {
            _1374_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1373_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1372_j)));
          }
          _1368_hashRhs = (_1368_hashRhs).Then(((RAST.Expr.create_Identifier(_1374_patternName)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          _1371_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1371_ctorMatchInner, _1374_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1372_j).Sign == 1) {
            _1367_printRhs = (_1367_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1367_printRhs = (_1367_printRhs).Then(RAST.Expr.create_RawExpr((((_1375_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1374_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1376_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1377_formalTpe;
          RAST._IType _out84;
          _out84 = (this).GenType(_1375_formalType, DCOMP.GenTypeContext.@default());
          _1377_formalTpe = _out84;
          DAST._IType _1378_newFormalType;
          _1378_newFormalType = (_1375_formalType).Replace(_1341_coerceMap);
          RAST._IType _1379_newFormalTpe;
          _1379_newFormalTpe = (_1377_formalTpe).Replace(_1342_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1380_upcastConverter;
          _1380_upcastConverter = (this).UpcastConversionLambda(_1375_formalType, _1377_formalTpe, _1378_newFormalType, _1379_newFormalTpe, _1343_coerceMapToArg);
          if ((_1380_upcastConverter).is_Success) {
            RAST._IExpr _1381_coercionFunction;
            _1381_coercionFunction = (_1380_upcastConverter).dtor_value;
            _1376_coerceRhsArg = (_1381_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1374_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1372_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1301_datatypeName));
            _1376_coerceRhsArg = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("todo!"))).Apply1(RAST.Expr.create_LiteralString((this.error).dtor_value, false, false));
          }
          _1369_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1369_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1374_patternName, _1376_coerceRhsArg)));
        }
        RAST._IExpr _1382_coerceRhs;
        _1382_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1301_datatypeName)).MSel(DCOMP.__default.escapeName((_1363_ctor).dtor_name)), _1369_coerceRhsArgs);
        if (_1370_isNumeric) {
          _1364_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1364_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1371_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1364_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1364_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1371_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1363_ctor).dtor_hasAnyArgs) {
          _1367_printRhs = (_1367_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1367_printRhs = (_1367_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1359_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1359_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1301_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1364_ctorMatch), RAST.Expr.create_Block(_1367_printRhs))));
        _1360_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1360_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1301_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1364_ctorMatch), RAST.Expr.create_Block(_1368_hashRhs))));
        _1361_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1361_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1301_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1364_ctorMatch), RAST.Expr.create_Block(_1382_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1383_extraCases;
        _1383_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1301_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}"))));
        _1359_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1359_printImplBodyCases, _1383_extraCases);
        _1360_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1360_hashImplBodyCases, _1383_extraCases);
        _1361_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1361_coerceImplBodyCases, _1383_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1384_defaultConstrainedTypeParams;
      _1384_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1299_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1385_rTypeParamsDeclsWithEq;
      _1385_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1299_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1386_rTypeParamsDeclsWithHash;
      _1386_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1299_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1387_printImplBody;
      _1387_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1359_printImplBodyCases);
      RAST._IExpr _1388_hashImplBody;
      _1388_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1360_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1299_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1299_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1387_printImplBody))))))));
      if ((new BigInteger((_1339_rCoerceTypeParams).Count)).Sign == 1) {
        RAST._IExpr _1389_coerceImplBody;
        _1389_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1361_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1299_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1339_rCoerceTypeParams, _1340_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1338_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.Type.create_SelfOwned())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1338_coerceTypes)), _1389_coerceImplBody))))))))));
      }
      if (_1358_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1385_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1386_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1388_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1390_structName;
        _1390_structName = (RAST.Expr.create_Identifier(_1301_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1391_structAssignments;
        _1391_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi21 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1392_i = BigInteger.Zero; _1392_i < _hi21; _1392_i++) {
          DAST._IDatatypeDtor _1393_dtor;
          _1393_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1392_i);
          _1391_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1391_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1393_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1394_defaultConstrainedTypeParams;
        _1394_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1299_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1395_fullType;
        _1395_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams);
        if (_1358_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1394_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1395_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1395_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1390_structName, _1391_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1299_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1395_fullType), RAST.Type.create_Borrowed(_1395_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        for (BigInteger _1396_i = BigInteger.Zero; _1396_i < _hi22; _1396_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1396_i))));
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
        for (BigInteger _1397_i = BigInteger.Zero; _1397_i < _hi23; _1397_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1397_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi24 = new BigInteger((args).Count);
      for (BigInteger _1398_i = BigInteger.Zero; _1398_i < _hi24; _1398_i++) {
        RAST._IType _1399_genTp;
        RAST._IType _out85;
        _out85 = (this).GenType((args).Select(_1398_i), genTypeContext);
        _1399_genTp = _out85;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1399_genTp));
      }
      return s;
    }
    public bool IsRcWrapped(Dafny.ISequence<DAST._IAttribute> attributes) {
      return ((!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("auto-nongrowing-size"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements()))) && (!(attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("false")))))) || ((attributes).Contains(DAST.Attribute.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rust_rc"), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("true")))));
    }
    public RAST._IType GenType(DAST._IType c, DCOMP._IGenTypeContext genTypeContext)
    {
      RAST._IType s = RAST.Type.Default();
      DAST._IType _source61 = c;
      bool unmatched61 = true;
      if (unmatched61) {
        if (_source61.is_UserDefined) {
          DAST._IResolvedType _1400_resolved = _source61.dtor_resolved;
          unmatched61 = false;
          {
            RAST._IType _1401_t;
            RAST._IType _out86;
            _out86 = DCOMP.COMP.GenPath((_1400_resolved).dtor_path);
            _1401_t = _out86;
            Dafny.ISequence<RAST._IType> _1402_typeArgs;
            Dafny.ISequence<RAST._IType> _out87;
            _out87 = (this).GenTypeArgs((_1400_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _1403_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _1404_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1403_dt__update__tmp_h0).dtor_inBinding, (_1403_dt__update__tmp_h0).dtor_inFn, _1404_dt__update_hforTraitParents_h0))))));
            _1402_typeArgs = _out87;
            s = RAST.Type.create_TypeApp(_1401_t, _1402_typeArgs);
            DAST._IResolvedTypeBase _source62 = (_1400_resolved).dtor_kind;
            bool unmatched62 = true;
            if (unmatched62) {
              if (_source62.is_Class) {
                unmatched62 = false;
                {
                  s = (this).Object(s);
                }
              }
            }
            if (unmatched62) {
              if (_source62.is_Datatype) {
                Dafny.ISequence<DAST._IVariance> _1405___v67 = _source62.dtor_variances;
                unmatched62 = false;
                {
                  if ((this).IsRcWrapped((_1400_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched62) {
              if (_source62.is_Trait) {
                unmatched62 = false;
                {
                  if (((_1400_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched62) {
              DAST._IType _1406_t = _source62.dtor_baseType;
              DAST._INewtypeRange _1407_range = _source62.dtor_range;
              bool _1408_erased = _source62.dtor_erase;
              unmatched62 = false;
              {
                if (_1408_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source63 = DCOMP.COMP.NewtypeToRustType(_1406_t, _1407_range);
                  bool unmatched63 = true;
                  if (unmatched63) {
                    if (_source63.is_Some) {
                      RAST._IType _1409_v = _source63.dtor_value;
                      unmatched63 = false;
                      s = _1409_v;
                    }
                  }
                  if (unmatched63) {
                    unmatched63 = false;
                  }
                }
              }
            }
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Object) {
          unmatched61 = false;
          {
            s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
            if (!((genTypeContext).dtor_forTraitParents)) {
              s = (this).Object(RAST.Type.create_DynType(s));
            }
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Tuple) {
          Dafny.ISequence<DAST._IType> _1410_types = _source61.dtor_Tuple_a0;
          unmatched61 = false;
          {
            Dafny.ISequence<RAST._IType> _1411_args;
            _1411_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1412_i;
            _1412_i = BigInteger.Zero;
            while ((_1412_i) < (new BigInteger((_1410_types).Count))) {
              RAST._IType _1413_generated;
              RAST._IType _out88;
              _out88 = (this).GenType((_1410_types).Select(_1412_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _1414_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _1415_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1414_dt__update__tmp_h1).dtor_inBinding, (_1414_dt__update__tmp_h1).dtor_inFn, _1415_dt__update_hforTraitParents_h1))))));
              _1413_generated = _out88;
              _1411_args = Dafny.Sequence<RAST._IType>.Concat(_1411_args, Dafny.Sequence<RAST._IType>.FromElements(_1413_generated));
              _1412_i = (_1412_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1410_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1411_args)) : (RAST.__default.SystemTupleType(_1411_args)));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Array) {
          DAST._IType _1416_element = _source61.dtor_element;
          BigInteger _1417_dims = _source61.dtor_dims;
          unmatched61 = false;
          {
            if ((_1417_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1418_elem;
              RAST._IType _out89;
              _out89 = (this).GenType(_1416_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _1419_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _1420_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1419_dt__update__tmp_h2).dtor_inBinding, (_1419_dt__update__tmp_h2).dtor_inFn, _1420_dt__update_hforTraitParents_h2))))));
              _1418_elem = _out89;
              if ((_1417_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1418_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1421_n;
                _1421_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1417_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1421_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1418_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Seq) {
          DAST._IType _1422_element = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1423_elem;
            RAST._IType _out90;
            _out90 = (this).GenType(_1422_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _1424_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _1425_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1424_dt__update__tmp_h3).dtor_inBinding, (_1424_dt__update__tmp_h3).dtor_inFn, _1425_dt__update_hforTraitParents_h3))))));
            _1423_elem = _out90;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1423_elem));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Set) {
          DAST._IType _1426_element = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1427_elem;
            RAST._IType _out91;
            _out91 = (this).GenType(_1426_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _1428_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _1429_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1428_dt__update__tmp_h4).dtor_inBinding, (_1428_dt__update__tmp_h4).dtor_inFn, _1429_dt__update_hforTraitParents_h4))))));
            _1427_elem = _out91;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1427_elem));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Multiset) {
          DAST._IType _1430_element = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1431_elem;
            RAST._IType _out92;
            _out92 = (this).GenType(_1430_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _1432_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _1433_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1432_dt__update__tmp_h5).dtor_inBinding, (_1432_dt__update__tmp_h5).dtor_inFn, _1433_dt__update_hforTraitParents_h5))))));
            _1431_elem = _out92;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1431_elem));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Map) {
          DAST._IType _1434_key = _source61.dtor_key;
          DAST._IType _1435_value = _source61.dtor_value;
          unmatched61 = false;
          {
            RAST._IType _1436_keyType;
            RAST._IType _out93;
            _out93 = (this).GenType(_1434_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _1437_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _1438_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1437_dt__update__tmp_h6).dtor_inBinding, (_1437_dt__update__tmp_h6).dtor_inFn, _1438_dt__update_hforTraitParents_h6))))));
            _1436_keyType = _out93;
            RAST._IType _1439_valueType;
            RAST._IType _out94;
            _out94 = (this).GenType(_1435_value, genTypeContext);
            _1439_valueType = _out94;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1436_keyType, _1439_valueType));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_MapBuilder) {
          DAST._IType _1440_key = _source61.dtor_key;
          DAST._IType _1441_value = _source61.dtor_value;
          unmatched61 = false;
          {
            RAST._IType _1442_keyType;
            RAST._IType _out95;
            _out95 = (this).GenType(_1440_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _1443_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _1444_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1443_dt__update__tmp_h7).dtor_inBinding, (_1443_dt__update__tmp_h7).dtor_inFn, _1444_dt__update_hforTraitParents_h7))))));
            _1442_keyType = _out95;
            RAST._IType _1445_valueType;
            RAST._IType _out96;
            _out96 = (this).GenType(_1441_value, genTypeContext);
            _1445_valueType = _out96;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1442_keyType, _1445_valueType));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_SetBuilder) {
          DAST._IType _1446_elem = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1447_elemType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1446_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _1448_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _1449_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1448_dt__update__tmp_h8).dtor_inBinding, (_1448_dt__update__tmp_h8).dtor_inFn, _1449_dt__update_hforTraitParents_h8))))));
            _1447_elemType = _out97;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1447_elemType));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1450_args = _source61.dtor_args;
          DAST._IType _1451_result = _source61.dtor_result;
          unmatched61 = false;
          {
            Dafny.ISequence<RAST._IType> _1452_argTypes;
            _1452_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1453_i;
            _1453_i = BigInteger.Zero;
            while ((_1453_i) < (new BigInteger((_1450_args).Count))) {
              RAST._IType _1454_generated;
              RAST._IType _out98;
              _out98 = (this).GenType((_1450_args).Select(_1453_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let29_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let29_0, _1455_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let30_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let30_0, _1456_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let31_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let31_0, _1457_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1455_dt__update__tmp_h9).dtor_inBinding, _1457_dt__update_hinFn_h0, _1456_dt__update_hforTraitParents_h9))))))));
              _1454_generated = _out98;
              _1452_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1452_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1454_generated)));
              _1453_i = (_1453_i) + (BigInteger.One);
            }
            RAST._IType _1458_resultType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1451_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1458_resultType = _out99;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1452_argTypes, _1458_resultType)));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source61.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1459_name = _h90;
          unmatched61 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1459_name));
        }
      }
      if (unmatched61) {
        if (_source61.is_Primitive) {
          DAST._IPrimitive _1460_p = _source61.dtor_Primitive_a0;
          unmatched61 = false;
          {
            DAST._IPrimitive _source64 = _1460_p;
            bool unmatched64 = true;
            if (unmatched64) {
              if (_source64.is_Int) {
                unmatched64 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyInt"));
              }
            }
            if (unmatched64) {
              if (_source64.is_Real) {
                unmatched64 = false;
                s = (RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("BigRational"));
              }
            }
            if (unmatched64) {
              if (_source64.is_String) {
                unmatched64 = false;
                s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements((RAST.__default.dafny__runtime__type).MSel((this).DafnyChar)));
              }
            }
            if (unmatched64) {
              if (_source64.is_Bool) {
                unmatched64 = false;
                s = RAST.Type.create_Bool();
              }
            }
            if (unmatched64) {
              unmatched64 = false;
              s = (RAST.__default.dafny__runtime__type).MSel((this).DafnyChar);
            }
          }
        }
      }
      if (unmatched61) {
        Dafny.ISequence<Dafny.Rune> _1461_v = _source61.dtor_Passthrough_a0;
        unmatched61 = false;
        s = RAST.__default.RawType(_1461_v);
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
      for (BigInteger _1462_i = BigInteger.Zero; _1462_i < _hi25; _1462_i++) {
        DAST._IMethod _source65 = (body).Select(_1462_i);
        bool unmatched65 = true;
        if (unmatched65) {
          DAST._IMethod _1463_m = _source65;
          unmatched65 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source66 = (_1463_m).dtor_overridingPath;
            bool unmatched66 = true;
            if (unmatched66) {
              if (_source66.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1464_p = _source66.dtor_value;
                unmatched66 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1465_existing;
                  _1465_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1464_p)) {
                    _1465_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1464_p);
                  }
                  if (((new BigInteger(((_1463_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1466_genMethod;
                  RAST._IImplMember _out100;
                  _out100 = (this).GenMethod(_1463_m, true, enclosingType, enclosingTypeParams);
                  _1466_genMethod = _out100;
                  _1465_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1465_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1466_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1464_p, _1465_existing)));
                }
              }
            }
            if (unmatched66) {
              unmatched66 = false;
              {
                RAST._IImplMember _1467_generated;
                RAST._IImplMember _out101;
                _out101 = (this).GenMethod(_1463_m, forTrait, enclosingType, enclosingTypeParams);
                _1467_generated = _out101;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1467_generated));
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
      for (BigInteger _1468_i = BigInteger.Zero; _1468_i < _hi26; _1468_i++) {
        DAST._IFormal _1469_param;
        _1469_param = (@params).Select(_1468_i);
        RAST._IType _1470_paramType;
        RAST._IType _out102;
        _out102 = (this).GenType((_1469_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1470_paramType = _out102;
        if ((!((_1470_paramType).CanReadWithoutClone())) && (!((_1469_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1470_paramType = RAST.Type.create_Borrowed(_1470_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1469_param).dtor_name), _1470_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1471_params;
      Dafny.ISequence<RAST._IFormal> _out103;
      _out103 = (this).GenParams((m).dtor_params);
      _1471_params = _out103;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1472_paramNames;
      _1472_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1473_paramTypes;
      _1473_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi27 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1474_paramI = BigInteger.Zero; _1474_paramI < _hi27; _1474_paramI++) {
        DAST._IFormal _1475_dafny__formal;
        _1475_dafny__formal = ((m).dtor_params).Select(_1474_paramI);
        RAST._IFormal _1476_formal;
        _1476_formal = (_1471_params).Select(_1474_paramI);
        Dafny.ISequence<Dafny.Rune> _1477_name;
        _1477_name = (_1476_formal).dtor_name;
        _1472_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1472_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1477_name));
        _1473_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1473_paramTypes, _1477_name, (_1476_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1478_fnName;
      _1478_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1479_selfIdent;
      _1479_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1480_selfId;
        _1480_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((m).dtor_outVarsAreUninitFieldsToAssign) {
          _1480_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv137 = enclosingTypeParams;
        var _pat_let_tv138 = enclosingType;
        DAST._IType _1481_instanceType;
        _1481_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source67 = enclosingType;
          bool unmatched67 = true;
          if (unmatched67) {
            if (_source67.is_UserDefined) {
              DAST._IResolvedType _1482_r = _source67.dtor_resolved;
              unmatched67 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1482_r, _pat_let32_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let32_0, _1483_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv137, _pat_let33_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let33_0, _1484_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1483_dt__update__tmp_h0).dtor_path, _1484_dt__update_htypeArgs_h0, (_1483_dt__update__tmp_h0).dtor_kind, (_1483_dt__update__tmp_h0).dtor_attributes, (_1483_dt__update__tmp_h0).dtor_properMethods, (_1483_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched67) {
            DAST._IType _1485___v68 = _source67;
            unmatched67 = false;
            return _pat_let_tv138;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1486_selfFormal;
          _1486_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1471_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1486_selfFormal), _1471_params);
        } else {
          RAST._IType _1487_tpe;
          RAST._IType _out104;
          _out104 = (this).GenType(_1481_instanceType, DCOMP.GenTypeContext.@default());
          _1487_tpe = _out104;
          if ((_1480_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1487_tpe = RAST.Type.create_Borrowed(_1487_tpe);
          } else if ((_1480_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1487_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1487_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1487_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              _1487_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.Type.create_SelfOwned()));
            }
          }
          _1471_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1480_selfId, _1487_tpe)), _1471_params);
        }
        _1479_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1480_selfId, _1481_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1488_retTypeArgs;
      _1488_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1489_typeI;
      _1489_typeI = BigInteger.Zero;
      while ((_1489_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1490_typeExpr;
        RAST._IType _out105;
        _out105 = (this).GenType(((m).dtor_outTypes).Select(_1489_typeI), DCOMP.GenTypeContext.@default());
        _1490_typeExpr = _out105;
        _1488_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1488_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1490_typeExpr));
        _1489_typeI = (_1489_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1491_visibility;
      _1491_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1492_typeParamsFiltered;
      _1492_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1493_typeParamI = BigInteger.Zero; _1493_typeParamI < _hi28; _1493_typeParamI++) {
        DAST._ITypeArgDecl _1494_typeParam;
        _1494_typeParam = ((m).dtor_typeParams).Select(_1493_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1494_typeParam).dtor_name)))) {
          _1492_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1492_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1494_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1495_typeParams;
      _1495_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1492_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi29 = new BigInteger((_1492_typeParamsFiltered).Count);
        for (BigInteger _1496_i = BigInteger.Zero; _1496_i < _hi29; _1496_i++) {
          DAST._IType _1497_typeArg;
          RAST._ITypeParamDecl _1498_rTypeParamDecl;
          DAST._IType _out106;
          RAST._ITypeParamDecl _out107;
          (this).GenTypeParam((_1492_typeParamsFiltered).Select(_1496_i), out _out106, out _out107);
          _1497_typeArg = _out106;
          _1498_rTypeParamDecl = _out107;
          var _pat_let_tv139 = _1498_rTypeParamDecl;
          _1498_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1498_rTypeParamDecl, _pat_let34_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let34_0, _1499_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv139).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let35_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let35_0, _1500_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1499_dt__update__tmp_h1).dtor_content, _1500_dt__update_hconstraints_h0)))));
          _1495_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1495_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1498_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1501_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1502_env = DCOMP.Environment.Default();
      RAST._IExpr _1503_preBody;
      _1503_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1504_preAssignNames;
      _1504_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1505_preAssignTypes;
      _1505_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        RAST._IExpr _1506_earlyReturn;
        _1506_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source68 = (m).dtor_outVars;
        bool unmatched68 = true;
        if (unmatched68) {
          if (_source68.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1507_outVars = _source68.dtor_value;
            unmatched68 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1506_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(Dafny.Sequence<RAST._IExpr>.FromElements())));
                BigInteger _hi30 = new BigInteger((_1507_outVars).Count);
                for (BigInteger _1508_outI = BigInteger.Zero; _1508_outI < _hi30; _1508_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1509_outVar;
                  _1509_outVar = (_1507_outVars).Select(_1508_outI);
                  Dafny.ISequence<Dafny.Rune> _1510_outName;
                  _1510_outName = DCOMP.__default.escapeName((_1509_outVar));
                  Dafny.ISequence<Dafny.Rune> _1511_tracker__name;
                  _1511_tracker__name = DCOMP.__default.AddAssignedPrefix(_1510_outName);
                  _1504_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1504_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1511_tracker__name));
                  _1505_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1505_preAssignTypes, _1511_tracker__name, RAST.Type.create_Bool());
                  _1503_preBody = (_1503_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1511_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<RAST._IExpr> _1512_tupleArgs;
                _1512_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
                BigInteger _hi31 = new BigInteger((_1507_outVars).Count);
                for (BigInteger _1513_outI = BigInteger.Zero; _1513_outI < _hi31; _1513_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1514_outVar;
                  _1514_outVar = (_1507_outVars).Select(_1513_outI);
                  RAST._IType _1515_outType;
                  RAST._IType _out108;
                  _out108 = (this).GenType(((m).dtor_outTypes).Select(_1513_outI), DCOMP.GenTypeContext.@default());
                  _1515_outType = _out108;
                  Dafny.ISequence<Dafny.Rune> _1516_outName;
                  _1516_outName = DCOMP.__default.escapeName((_1514_outVar));
                  _1472_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1472_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1516_outName));
                  RAST._IType _1517_outMaybeType;
                  _1517_outMaybeType = (((_1515_outType).CanReadWithoutClone()) ? (_1515_outType) : (RAST.__default.MaybePlaceboType(_1515_outType)));
                  _1473_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1473_paramTypes, _1516_outName, _1517_outMaybeType);
                  RAST._IExpr _1518_outVarReturn;
                  DCOMP._IOwnership _1519___v69;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1520___v70;
                  RAST._IExpr _out109;
                  DCOMP._IOwnership _out110;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
                  (this).GenExpr(DAST.Expression.create_Ident((_1514_outVar)), DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1516_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1516_outName, _1517_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out109, out _out110, out _out111);
                  _1518_outVarReturn = _out109;
                  _1519___v69 = _out110;
                  _1520___v70 = _out111;
                  _1512_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1512_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1518_outVarReturn));
                }
                if ((new BigInteger((_1512_tupleArgs).Count)) == (BigInteger.One)) {
                  _1506_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1512_tupleArgs).Select(BigInteger.Zero)));
                } else {
                  _1506_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1512_tupleArgs)));
                }
              }
            }
          }
        }
        if (unmatched68) {
          unmatched68 = false;
        }
        _1502_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1504_preAssignNames, _1472_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1505_preAssignTypes, _1473_paramTypes));
        RAST._IExpr _1521_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1522___v71;
        DCOMP._IEnvironment _1523___v72;
        RAST._IExpr _out112;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out113;
        DCOMP._IEnvironment _out114;
        (this).GenStmts((m).dtor_body, _1479_selfIdent, _1502_env, true, _1506_earlyReturn, out _out112, out _out113, out _out114);
        _1521_body = _out112;
        _1522___v71 = _out113;
        _1523___v72 = _out114;
        _1501_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1503_preBody).Then(_1521_body));
      } else {
        _1502_env = DCOMP.Environment.create(_1472_paramNames, _1473_paramTypes);
        _1501_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1491_visibility, RAST.Fn.create(_1478_fnName, _1495_typeParams, _1471_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1488_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1488_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1488_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1501_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1524_declarations;
      _1524_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1525_i;
      _1525_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1526_stmts;
      _1526_stmts = stmts;
      while ((_1525_i) < (new BigInteger((_1526_stmts).Count))) {
        DAST._IStatement _1527_stmt;
        _1527_stmt = (_1526_stmts).Select(_1525_i);
        DAST._IStatement _source69 = _1527_stmt;
        bool unmatched69 = true;
        if (unmatched69) {
          if (_source69.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1528_name = _source69.dtor_name;
            DAST._IType _1529_optType = _source69.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source69.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched69 = false;
              if (((_1525_i) + (BigInteger.One)) < (new BigInteger((_1526_stmts).Count))) {
                DAST._IStatement _source70 = (_1526_stmts).Select((_1525_i) + (BigInteger.One));
                bool unmatched70 = true;
                if (unmatched70) {
                  if (_source70.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source70.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _1530_name2 = ident0;
                      DAST._IExpression _1531_rhs = _source70.dtor_value;
                      unmatched70 = false;
                      if (object.Equals(_1530_name2, _1528_name)) {
                        _1526_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1526_stmts).Subsequence(BigInteger.Zero, _1525_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1528_name, _1529_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1531_rhs)))), (_1526_stmts).Drop((_1525_i) + (new BigInteger(2))));
                        _1527_stmt = (_1526_stmts).Select(_1525_i);
                      }
                    }
                  }
                }
                if (unmatched70) {
                  DAST._IStatement _1532___v73 = _source70;
                  unmatched70 = false;
                }
              }
            }
          }
        }
        if (unmatched69) {
          DAST._IStatement _1533___v74 = _source69;
          unmatched69 = false;
        }
        RAST._IExpr _1534_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1535_recIdents;
        DCOMP._IEnvironment _1536_newEnv2;
        RAST._IExpr _out115;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
        DCOMP._IEnvironment _out117;
        (this).GenStmt(_1527_stmt, selfIdent, newEnv, (isLast) && ((_1525_i) == ((new BigInteger((_1526_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out115, out _out116, out _out117);
        _1534_stmtExpr = _out115;
        _1535_recIdents = _out116;
        _1536_newEnv2 = _out117;
        newEnv = _1536_newEnv2;
        DAST._IStatement _source71 = _1527_stmt;
        bool unmatched71 = true;
        if (unmatched71) {
          if (_source71.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1537_name = _source71.dtor_name;
            DAST._IType _1538___v75 = _source71.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> _1539___v76 = _source71.dtor_maybeValue;
            unmatched71 = false;
            {
              _1524_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1524_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1537_name)));
            }
          }
        }
        if (unmatched71) {
          DAST._IStatement _1540___v77 = _source71;
          unmatched71 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1535_recIdents, _1524_declarations));
        generated = (generated).Then(_1534_stmtExpr);
        _1525_i = (_1525_i) + (BigInteger.One);
        if ((_1534_stmtExpr).is_Return) {
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
      DAST._IAssignLhs _source72 = lhs;
      bool unmatched72 = true;
      if (unmatched72) {
        if (_source72.is_Ident) {
          Dafny.ISequence<Dafny.Rune> ident1 = _source72.dtor_ident;
          Dafny.ISequence<Dafny.Rune> _1541_id = ident1;
          unmatched72 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1542_idRust;
            _1542_idRust = DCOMP.__default.escapeName(_1541_id);
            if (((env).IsBorrowed(_1542_idRust)) || ((env).IsBorrowedMut(_1542_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1542_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1542_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1542_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched72) {
        if (_source72.is_Select) {
          DAST._IExpression _1543_on = _source72.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1544_field = _source72.dtor_field;
          unmatched72 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1545_fieldName;
            _1545_fieldName = DCOMP.__default.escapeName(_1544_field);
            RAST._IExpr _1546_onExpr;
            DCOMP._IOwnership _1547_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1548_recIdents;
            RAST._IExpr _out118;
            DCOMP._IOwnership _out119;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
            (this).GenExpr(_1543_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out118, out _out119, out _out120);
            _1546_onExpr = _out118;
            _1547_onOwned = _out119;
            _1548_recIdents = _out120;
            RAST._IExpr _source73 = _1546_onExpr;
            bool unmatched73 = true;
            if (unmatched73) {
              bool disjunctiveMatch11 = false;
              if (_source73.is_Call) {
                RAST._IExpr obj2 = _source73.dtor_obj;
                if (obj2.is_Select) {
                  RAST._IExpr obj3 = obj2.dtor_obj;
                  if (obj3.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name11 = obj3.dtor_name;
                    if (object.Equals(name11, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      Dafny.ISequence<Dafny.Rune> name12 = obj2.dtor_name;
                      if (object.Equals(name12, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("clone"))) {
                        Dafny.ISequence<RAST._IExpr> _1549___v78 = _source73.dtor_arguments;
                        disjunctiveMatch11 = true;
                      }
                    }
                  }
                }
              }
              if (_source73.is_Identifier) {
                Dafny.ISequence<Dafny.Rune> name13 = _source73.dtor_name;
                if (object.Equals(name13, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                  disjunctiveMatch11 = true;
                }
              }
              if (_source73.is_UnaryOp) {
                Dafny.ISequence<Dafny.Rune> op14 = _source73.dtor_op1;
                if (object.Equals(op14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                  RAST._IExpr underlying4 = _source73.dtor_underlying;
                  if (underlying4.is_Identifier) {
                    Dafny.ISequence<Dafny.Rune> name14 = underlying4.dtor_name;
                    if (object.Equals(name14, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                      DAST.Format._IUnaryOpFormat _1550___v79 = _source73.dtor_format;
                      disjunctiveMatch11 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch11) {
                unmatched73 = false;
                Dafny.ISequence<Dafny.Rune> _1551_isAssignedVar;
                _1551_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1545_fieldName);
                if (((newEnv).dtor_names).Contains(_1551_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1545_fieldName), RAST.Expr.create_Identifier(_1551_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1551_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1551_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1545_fieldName, rhs);
                }
              }
            }
            if (unmatched73) {
              RAST._IExpr _1552___v80 = _source73;
              unmatched73 = false;
              if (!object.Equals(_1546_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1546_onExpr = ((this).modify__macro).Apply1(_1546_onExpr);
              }
              generated = RAST.__default.AssignMember(_1546_onExpr, _1545_fieldName, rhs);
            }
            readIdents = _1548_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched72) {
        DAST._IExpression _1553_on = _source72.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1554_indices = _source72.dtor_indices;
        unmatched72 = false;
        {
          RAST._IExpr _1555_onExpr;
          DCOMP._IOwnership _1556_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1557_recIdents;
          RAST._IExpr _out121;
          DCOMP._IOwnership _out122;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
          (this).GenExpr(_1553_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out121, out _out122, out _out123);
          _1555_onExpr = _out121;
          _1556_onOwned = _out122;
          _1557_recIdents = _out123;
          readIdents = _1557_recIdents;
          _1555_onExpr = ((this).modify__macro).Apply1(_1555_onExpr);
          RAST._IExpr _1558_r;
          _1558_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1559_indicesExpr;
          _1559_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_1554_indices).Count);
          for (BigInteger _1560_i = BigInteger.Zero; _1560_i < _hi32; _1560_i++) {
            RAST._IExpr _1561_idx;
            DCOMP._IOwnership _1562___v81;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1563_recIdentsIdx;
            RAST._IExpr _out124;
            DCOMP._IOwnership _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            (this).GenExpr((_1554_indices).Select(_1560_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out124, out _out125, out _out126);
            _1561_idx = _out124;
            _1562___v81 = _out125;
            _1563_recIdentsIdx = _out126;
            Dafny.ISequence<Dafny.Rune> _1564_varName;
            _1564_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1560_i));
            _1559_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1559_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1564_varName)));
            _1558_r = (_1558_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1564_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), (_1561_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1563_recIdentsIdx);
          }
          if ((new BigInteger((_1554_indices).Count)) > (BigInteger.One)) {
            _1555_onExpr = (_1555_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1565_rhs;
          _1565_rhs = rhs;
          var _pat_let_tv140 = env;
          if (((_1555_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1555_onExpr).LhsIdentifierName(), _pat_let36_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let36_0, _1566_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv140).GetType(_1566_name), _pat_let37_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let37_0, _1567_tpe => ((_1567_tpe).is_Some) && (((_1567_tpe).dtor_value).IsUninitArray())))))))) {
            _1565_rhs = RAST.__default.MaybeUninitNew(_1565_rhs);
          }
          generated = (_1558_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1555_onExpr, _1559_indicesExpr)), _1565_rhs));
          needsIIFE = true;
        }
      }
    }
    public void GenStmt(DAST._IStatement stmt, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      DAST._IStatement _source74 = stmt;
      bool unmatched74 = true;
      if (unmatched74) {
        if (_source74.is_ConstructorNewSeparator) {
          Dafny.ISequence<DAST._IFormal> _1568_fields = _source74.dtor_fields;
          unmatched74 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi33 = new BigInteger((_1568_fields).Count);
            for (BigInteger _1569_i = BigInteger.Zero; _1569_i < _hi33; _1569_i++) {
              DAST._IFormal _1570_field;
              _1570_field = (_1568_fields).Select(_1569_i);
              Dafny.ISequence<Dafny.Rune> _1571_fieldName;
              _1571_fieldName = DCOMP.__default.escapeName((_1570_field).dtor_name);
              RAST._IType _1572_fieldTyp;
              RAST._IType _out127;
              _out127 = (this).GenType((_1570_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1572_fieldTyp = _out127;
              Dafny.ISequence<Dafny.Rune> _1573_isAssignedVar;
              _1573_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1571_fieldName);
              if (((newEnv).dtor_names).Contains(_1573_isAssignedVar)) {
                RAST._IExpr _1574_rhs;
                DCOMP._IOwnership _1575___v82;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1576___v83;
                RAST._IExpr _out128;
                DCOMP._IOwnership _out129;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1570_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out128, out _out129, out _out130);
                _1574_rhs = _out128;
                _1575___v82 = _out129;
                _1576___v83 = _out130;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1573_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1571_fieldName), RAST.Expr.create_Identifier(_1573_isAssignedVar), _1574_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1573_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1577_name = _source74.dtor_name;
          DAST._IType _1578_typ = _source74.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source74.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1579_expression = maybeValue1.dtor_value;
            unmatched74 = false;
            {
              RAST._IType _1580_tpe;
              RAST._IType _out131;
              _out131 = (this).GenType(_1578_typ, DCOMP.GenTypeContext.InBinding());
              _1580_tpe = _out131;
              Dafny.ISequence<Dafny.Rune> _1581_varName;
              _1581_varName = DCOMP.__default.escapeName(_1577_name);
              bool _1582_hasCopySemantics;
              _1582_hasCopySemantics = (_1580_tpe).CanReadWithoutClone();
              if (((_1579_expression).is_InitializationValue) && (!(_1582_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1581_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1580_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1581_varName, RAST.__default.MaybePlaceboType(_1580_tpe));
              } else {
                RAST._IExpr _1583_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1584_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1579_expression).is_InitializationValue) && ((_1580_tpe).IsObjectOrPointer())) {
                  _1583_expr = (_1580_tpe).ToNullExpr();
                  _1584_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1585_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out132;
                  DCOMP._IOwnership _out133;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out134;
                  (this).GenExpr(_1579_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out132, out _out133, out _out134);
                  _1583_expr = _out132;
                  _1585_exprOwnership = _out133;
                  _1584_recIdents = _out134;
                }
                readIdents = _1584_recIdents;
                _1580_tpe = (((_1579_expression).is_NewUninitArray) ? ((_1580_tpe).TypeAtInitialization()) : (_1580_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1577_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1580_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1583_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1577_name), _1580_tpe);
              }
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1586_name = _source74.dtor_name;
          DAST._IType _1587_typ = _source74.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source74.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched74 = false;
            {
              DAST._IStatement _1588_newStmt;
              _1588_newStmt = DAST.Statement.create_DeclareVar(_1586_name, _1587_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1587_typ)));
              RAST._IExpr _out135;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out136;
              DCOMP._IEnvironment _out137;
              (this).GenStmt(_1588_newStmt, selfIdent, env, isLast, earlyReturn, out _out135, out _out136, out _out137);
              generated = _out135;
              readIdents = _out136;
              newEnv = _out137;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Assign) {
          DAST._IAssignLhs _1589_lhs = _source74.dtor_lhs;
          DAST._IExpression _1590_expression = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IExpr _1591_exprGen;
            DCOMP._IOwnership _1592___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1593_exprIdents;
            RAST._IExpr _out138;
            DCOMP._IOwnership _out139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
            (this).GenExpr(_1590_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out138, out _out139, out _out140);
            _1591_exprGen = _out138;
            _1592___v84 = _out139;
            _1593_exprIdents = _out140;
            if ((_1589_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1594_rustId;
              _1594_rustId = DCOMP.__default.escapeName(((_1589_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1595_tpe;
              _1595_tpe = (env).GetType(_1594_rustId);
              if (((_1595_tpe).is_Some) && ((((_1595_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1591_exprGen = RAST.__default.MaybePlacebo(_1591_exprGen);
              }
            }
            RAST._IExpr _1596_lhsGen;
            bool _1597_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1598_recIdents;
            DCOMP._IEnvironment _1599_resEnv;
            RAST._IExpr _out141;
            bool _out142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
            DCOMP._IEnvironment _out144;
            (this).GenAssignLhs(_1589_lhs, _1591_exprGen, selfIdent, env, out _out141, out _out142, out _out143, out _out144);
            _1596_lhsGen = _out141;
            _1597_needsIIFE = _out142;
            _1598_recIdents = _out143;
            _1599_resEnv = _out144;
            generated = _1596_lhsGen;
            newEnv = _1599_resEnv;
            if (_1597_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1598_recIdents, _1593_exprIdents);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_If) {
          DAST._IExpression _1600_cond = _source74.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1601_thnDafny = _source74.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1602_elsDafny = _source74.dtor_els;
          unmatched74 = false;
          {
            RAST._IExpr _1603_cond;
            DCOMP._IOwnership _1604___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1605_recIdents;
            RAST._IExpr _out145;
            DCOMP._IOwnership _out146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
            (this).GenExpr(_1600_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out145, out _out146, out _out147);
            _1603_cond = _out145;
            _1604___v85 = _out146;
            _1605_recIdents = _out147;
            Dafny.ISequence<Dafny.Rune> _1606_condString;
            _1606_condString = (_1603_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1605_recIdents;
            RAST._IExpr _1607_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1608_thnIdents;
            DCOMP._IEnvironment _1609_thnEnv;
            RAST._IExpr _out148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
            DCOMP._IEnvironment _out150;
            (this).GenStmts(_1601_thnDafny, selfIdent, env, isLast, earlyReturn, out _out148, out _out149, out _out150);
            _1607_thn = _out148;
            _1608_thnIdents = _out149;
            _1609_thnEnv = _out150;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1608_thnIdents);
            RAST._IExpr _1610_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1611_elsIdents;
            DCOMP._IEnvironment _1612_elsEnv;
            RAST._IExpr _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP._IEnvironment _out153;
            (this).GenStmts(_1602_elsDafny, selfIdent, env, isLast, earlyReturn, out _out151, out _out152, out _out153);
            _1610_els = _out151;
            _1611_elsIdents = _out152;
            _1612_elsEnv = _out153;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1611_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1603_cond, _1607_thn, _1610_els);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1613_lbl = _source74.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1614_body = _source74.dtor_body;
          unmatched74 = false;
          {
            RAST._IExpr _1615_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1616_bodyIdents;
            DCOMP._IEnvironment _1617_env2;
            RAST._IExpr _out154;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out155;
            DCOMP._IEnvironment _out156;
            (this).GenStmts(_1614_body, selfIdent, env, isLast, earlyReturn, out _out154, out _out155, out _out156);
            _1615_body = _out154;
            _1616_bodyIdents = _out155;
            _1617_env2 = _out156;
            readIdents = _1616_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1613_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1615_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_While) {
          DAST._IExpression _1618_cond = _source74.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1619_body = _source74.dtor_body;
          unmatched74 = false;
          {
            RAST._IExpr _1620_cond;
            DCOMP._IOwnership _1621___v86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1622_recIdents;
            RAST._IExpr _out157;
            DCOMP._IOwnership _out158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
            (this).GenExpr(_1618_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out157, out _out158, out _out159);
            _1620_cond = _out157;
            _1621___v86 = _out158;
            _1622_recIdents = _out159;
            readIdents = _1622_recIdents;
            RAST._IExpr _1623_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1624_bodyIdents;
            DCOMP._IEnvironment _1625_bodyEnv;
            RAST._IExpr _out160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out161;
            DCOMP._IEnvironment _out162;
            (this).GenStmts(_1619_body, selfIdent, env, false, earlyReturn, out _out160, out _out161, out _out162);
            _1623_bodyExpr = _out160;
            _1624_bodyIdents = _out161;
            _1625_bodyEnv = _out162;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1624_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1620_cond), _1623_bodyExpr);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1626_boundName = _source74.dtor_boundName;
          DAST._IType _1627_boundType = _source74.dtor_boundType;
          DAST._IExpression _1628_overExpr = _source74.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1629_body = _source74.dtor_body;
          unmatched74 = false;
          {
            RAST._IExpr _1630_over;
            DCOMP._IOwnership _1631___v87;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1632_recIdents;
            RAST._IExpr _out163;
            DCOMP._IOwnership _out164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
            (this).GenExpr(_1628_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out163, out _out164, out _out165);
            _1630_over = _out163;
            _1631___v87 = _out164;
            _1632_recIdents = _out165;
            if (((_1628_overExpr).is_MapBoundedPool) || ((_1628_overExpr).is_SetBoundedPool)) {
              _1630_over = ((_1630_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1633_boundTpe;
            RAST._IType _out166;
            _out166 = (this).GenType(_1627_boundType, DCOMP.GenTypeContext.@default());
            _1633_boundTpe = _out166;
            readIdents = _1632_recIdents;
            Dafny.ISequence<Dafny.Rune> _1634_boundRName;
            _1634_boundRName = DCOMP.__default.escapeName(_1626_boundName);
            RAST._IExpr _1635_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1636_bodyIdents;
            DCOMP._IEnvironment _1637_bodyEnv;
            RAST._IExpr _out167;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out168;
            DCOMP._IEnvironment _out169;
            (this).GenStmts(_1629_body, selfIdent, (env).AddAssigned(_1634_boundRName, _1633_boundTpe), false, earlyReturn, out _out167, out _out168, out _out169);
            _1635_bodyExpr = _out167;
            _1636_bodyIdents = _out168;
            _1637_bodyEnv = _out169;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1636_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1634_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1634_boundRName, _1630_over, _1635_bodyExpr);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1638_toLabel = _source74.dtor_toLabel;
          unmatched74 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source75 = _1638_toLabel;
            bool unmatched75 = true;
            if (unmatched75) {
              if (_source75.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1639_lbl = _source75.dtor_value;
                unmatched75 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1639_lbl)));
                }
              }
            }
            if (unmatched75) {
              unmatched75 = false;
              {
                generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
              }
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_TailRecursive) {
          Dafny.ISequence<DAST._IStatement> _1640_body = _source74.dtor_body;
          unmatched74 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1641_selfClone;
              DCOMP._IOwnership _1642___v88;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1643___v89;
              RAST._IExpr _out170;
              DCOMP._IOwnership _out171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out172;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out170, out _out171, out _out172);
              _1641_selfClone = _out170;
              _1642___v88 = _out171;
              _1643___v89 = _out172;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1641_selfClone)));
            }
            newEnv = env;
            BigInteger _hi34 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1644_paramI = BigInteger.Zero; _1644_paramI < _hi34; _1644_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1645_param;
              _1645_param = ((env).dtor_names).Select(_1644_paramI);
              RAST._IExpr _1646_paramInit;
              DCOMP._IOwnership _1647___v90;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1648___v91;
              RAST._IExpr _out173;
              DCOMP._IOwnership _out174;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out175;
              (this).GenIdent(_1645_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out173, out _out174, out _out175);
              _1646_paramInit = _out173;
              _1647___v90 = _out174;
              _1648___v91 = _out175;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1645_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1646_paramInit)));
              if (((env).dtor_types).Contains(_1645_param)) {
                RAST._IType _1649_declaredType;
                _1649_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1645_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1645_param, _1649_declaredType);
              }
            }
            RAST._IExpr _1650_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1651_bodyIdents;
            DCOMP._IEnvironment _1652_bodyEnv;
            RAST._IExpr _out176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
            DCOMP._IEnvironment _out178;
            (this).GenStmts(_1640_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out176, out _out177, out _out178);
            _1650_bodyExpr = _out176;
            _1651_bodyIdents = _out177;
            _1652_bodyEnv = _out178;
            readIdents = _1651_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1650_bodyExpr)));
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_JumpTailCallStart) {
          unmatched74 = false;
          {
            generated = RAST.Expr.create_Continue(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Call) {
          DAST._IExpression _1653_on = _source74.dtor_on;
          DAST._ICallName _1654_name = _source74.dtor_callName;
          Dafny.ISequence<DAST._IType> _1655_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1656_args = _source74.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1657_maybeOutVars = _source74.dtor_outs;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1658_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1659_recIdents;
            Dafny.ISequence<RAST._IType> _1660_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1661_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out180;
            Dafny.ISequence<RAST._IType> _out181;
            Std.Wrappers._IOption<DAST._IResolvedType> _out182;
            (this).GenArgs(selfIdent, _1654_name, _1655_typeArgs, _1656_args, env, out _out179, out _out180, out _out181, out _out182);
            _1658_argExprs = _out179;
            _1659_recIdents = _out180;
            _1660_typeExprs = _out181;
            _1661_fullNameQualifier = _out182;
            readIdents = _1659_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source76 = _1661_fullNameQualifier;
            bool unmatched76 = true;
            if (unmatched76) {
              if (_source76.is_Some) {
                DAST._IResolvedType value9 = _source76.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1662_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1663_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1664_base = value9.dtor_kind;
                Dafny.ISequence<DAST._IAttribute> _1665___v92 = value9.dtor_attributes;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1666___v93 = value9.dtor_properMethods;
                Dafny.ISequence<DAST._IType> _1667___v94 = value9.dtor_extendedTypes;
                unmatched76 = false;
                RAST._IExpr _1668_fullPath;
                RAST._IExpr _out183;
                _out183 = DCOMP.COMP.GenPathExpr(_1662_path);
                _1668_fullPath = _out183;
                Dafny.ISequence<RAST._IType> _1669_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out184;
                _out184 = (this).GenTypeArgs(_1663_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1669_onTypeExprs = _out184;
                RAST._IExpr _1670_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1671_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1672_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1664_base).is_Trait) || ((_1664_base).is_Class)) {
                  RAST._IExpr _out185;
                  DCOMP._IOwnership _out186;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out187;
                  (this).GenExpr(_1653_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out185, out _out186, out _out187);
                  _1670_onExpr = _out185;
                  _1671_recOwnership = _out186;
                  _1672_recIdents = _out187;
                  _1670_onExpr = ((this).modify__macro).Apply1(_1670_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1672_recIdents);
                } else {
                  RAST._IExpr _out188;
                  DCOMP._IOwnership _out189;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
                  (this).GenExpr(_1653_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out188, out _out189, out _out190);
                  _1670_onExpr = _out188;
                  _1671_recOwnership = _out189;
                  _1672_recIdents = _out190;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1672_recIdents);
                }
                generated = ((((_1668_fullPath).ApplyType(_1669_onTypeExprs)).MSel(DCOMP.__default.escapeName((_1654_name).dtor_name))).ApplyType(_1660_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1670_onExpr), _1658_argExprs));
              }
            }
            if (unmatched76) {
              Std.Wrappers._IOption<DAST._IResolvedType> _1673___v95 = _source76;
              unmatched76 = false;
              RAST._IExpr _1674_onExpr;
              DCOMP._IOwnership _1675___v96;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1676_enclosingIdents;
              RAST._IExpr _out191;
              DCOMP._IOwnership _out192;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
              (this).GenExpr(_1653_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out191, out _out192, out _out193);
              _1674_onExpr = _out191;
              _1675___v96 = _out192;
              _1676_enclosingIdents = _out193;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1676_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1677_renderedName;
              _1677_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
                DAST._ICallName _source77 = _1654_name;
                bool unmatched77 = true;
                if (unmatched77) {
                  if (_source77.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _1678_name = _source77.dtor_name;
                    Std.Wrappers._IOption<DAST._IType> _1679___v97 = _source77.dtor_onType;
                    Std.Wrappers._IOption<DAST._IFormal> _1680___v98 = _source77.dtor_receiverArgs;
                    Dafny.ISequence<DAST._IFormal> _1681___v99 = _source77.dtor_signature;
                    unmatched77 = false;
                    return DCOMP.__default.escapeName(_1678_name);
                  }
                }
                if (unmatched77) {
                  bool disjunctiveMatch12 = false;
                  if (_source77.is_MapBuilderAdd) {
                    disjunctiveMatch12 = true;
                  }
                  if (_source77.is_SetBuilderAdd) {
                    disjunctiveMatch12 = true;
                  }
                  if (disjunctiveMatch12) {
                    unmatched77 = false;
                    return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  }
                }
                if (unmatched77) {
                  bool disjunctiveMatch13 = false;
                  disjunctiveMatch13 = true;
                  disjunctiveMatch13 = true;
                  if (disjunctiveMatch13) {
                    unmatched77 = false;
                    return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                  }
                }
                throw new System.Exception("unexpected control point");
              }))();
              DAST._IExpression _source78 = _1653_on;
              bool unmatched78 = true;
              if (unmatched78) {
                if (_source78.is_Companion) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1682___v100 = _source78.dtor_Companion_a0;
                  Dafny.ISequence<DAST._IType> _1683___v101 = _source78.dtor_typeArgs;
                  unmatched78 = false;
                  {
                    _1674_onExpr = (_1674_onExpr).MSel(_1677_renderedName);
                  }
                }
              }
              if (unmatched78) {
                DAST._IExpression _1684___v102 = _source78;
                unmatched78 = false;
                {
                  if (!object.Equals(_1674_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source79 = _1654_name;
                    bool unmatched79 = true;
                    if (unmatched79) {
                      if (_source79.is_CallName) {
                        Dafny.ISequence<Dafny.Rune> _1685___v103 = _source79.dtor_name;
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source79.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1686_tpe = onType0.dtor_value;
                          Std.Wrappers._IOption<DAST._IFormal> _1687___v104 = _source79.dtor_receiverArgs;
                          Dafny.ISequence<DAST._IFormal> _1688___v105 = _source79.dtor_signature;
                          unmatched79 = false;
                          RAST._IType _1689_typ;
                          RAST._IType _out194;
                          _out194 = (this).GenType(_1686_tpe, DCOMP.GenTypeContext.@default());
                          _1689_typ = _out194;
                          if (((_1689_typ).IsObjectOrPointer()) && (!object.Equals(_1674_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1674_onExpr = ((this).modify__macro).Apply1(_1674_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched79) {
                      DAST._ICallName _1690___v106 = _source79;
                      unmatched79 = false;
                    }
                  }
                  _1674_onExpr = (_1674_onExpr).Sel(_1677_renderedName);
                }
              }
              generated = ((_1674_onExpr).ApplyType(_1660_typeExprs)).Apply(_1658_argExprs);
            }
            if (((_1657_maybeOutVars).is_Some) && ((new BigInteger(((_1657_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1691_outVar;
              _1691_outVar = DCOMP.__default.escapeName((((_1657_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1691_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1691_outVar, generated);
            } else if (((_1657_maybeOutVars).is_None) || ((new BigInteger(((_1657_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1692_tmpVar;
              _1692_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1693_tmpId;
              _1693_tmpId = RAST.Expr.create_Identifier(_1692_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1692_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1694_outVars;
              _1694_outVars = (_1657_maybeOutVars).dtor_value;
              BigInteger _hi35 = new BigInteger((_1694_outVars).Count);
              for (BigInteger _1695_outI = BigInteger.Zero; _1695_outI < _hi35; _1695_outI++) {
                Dafny.ISequence<Dafny.Rune> _1696_outVar;
                _1696_outVar = DCOMP.__default.escapeName(((_1694_outVars).Select(_1695_outI)));
                RAST._IExpr _1697_rhs;
                _1697_rhs = (_1693_tmpId).Sel(Std.Strings.__default.OfNat(_1695_outI));
                if (!((env).CanReadWithoutClone(_1696_outVar))) {
                  _1697_rhs = RAST.__default.MaybePlacebo(_1697_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1696_outVar, _1697_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Return) {
          DAST._IExpression _1698_exprDafny = _source74.dtor_expr;
          unmatched74 = false;
          {
            RAST._IExpr _1699_expr;
            DCOMP._IOwnership _1700___v107;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1701_recIdents;
            RAST._IExpr _out195;
            DCOMP._IOwnership _out196;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
            (this).GenExpr(_1698_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out195, out _out196, out _out197);
            _1699_expr = _out195;
            _1700___v107 = _out196;
            _1701_recIdents = _out197;
            readIdents = _1701_recIdents;
            if (isLast) {
              generated = _1699_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1699_expr));
            }
            newEnv = env;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_EarlyReturn) {
          unmatched74 = false;
          {
            generated = earlyReturn;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Halt) {
          unmatched74 = false;
          {
            generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!"))).Apply1(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Halt"), false, false));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
          }
        }
      }
      if (unmatched74) {
        DAST._IExpression _1702_e = _source74.dtor_Print_a0;
        unmatched74 = false;
        {
          RAST._IExpr _1703_printedExpr;
          DCOMP._IOwnership _1704_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1705_recIdents;
          RAST._IExpr _out198;
          DCOMP._IOwnership _out199;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out200;
          (this).GenExpr(_1702_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out198, out _out199, out _out200);
          _1703_printedExpr = _out198;
          _1704_recOwnership = _out199;
          _1705_recIdents = _out200;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1703_printedExpr)));
          readIdents = _1705_recIdents;
          newEnv = env;
        }
      }
    }
    public static Std.Wrappers._IOption<RAST._IType> NewtypeToRustType(DAST._IType @base, DAST._INewtypeRange range)
    {
      DAST._INewtypeRange _source80 = range;
      bool unmatched80 = true;
      if (unmatched80) {
        if (_source80.is_NoRange) {
          unmatched80 = false;
          return Std.Wrappers.Option<RAST._IType>.create_None();
        }
      }
      if (unmatched80) {
        if (_source80.is_U8) {
          unmatched80 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U8());
        }
      }
      if (unmatched80) {
        if (_source80.is_U16) {
          unmatched80 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U16());
        }
      }
      if (unmatched80) {
        if (_source80.is_U32) {
          unmatched80 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U32());
        }
      }
      if (unmatched80) {
        if (_source80.is_U64) {
          unmatched80 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U64());
        }
      }
      if (unmatched80) {
        if (_source80.is_U128) {
          unmatched80 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_U128());
        }
      }
      if (unmatched80) {
        if (_source80.is_I8) {
          unmatched80 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I8());
        }
      }
      if (unmatched80) {
        if (_source80.is_I16) {
          unmatched80 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I16());
        }
      }
      if (unmatched80) {
        if (_source80.is_I32) {
          unmatched80 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I32());
        }
      }
      if (unmatched80) {
        if (_source80.is_I64) {
          unmatched80 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I64());
        }
      }
      if (unmatched80) {
        if (_source80.is_I128) {
          unmatched80 = false;
          return Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_I128());
        }
      }
      if (unmatched80) {
        DAST._INewtypeRange _1706___v108 = _source80;
        unmatched80 = false;
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
        RAST._IExpr _out201;
        DCOMP._IOwnership _out202;
        (this).FromOwned(r, expectedOwnership, out _out201, out _out202);
        @out = _out201;
        resultingOwnership = _out202;
        return ;
      } else if (object.Equals(ownership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        RAST._IExpr _out203;
        DCOMP._IOwnership _out204;
        (this).FromOwned(RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), r, DAST.Format.UnaryOpFormat.create_NoFormat()), expectedOwnership, out _out203, out _out204);
        @out = _out203;
        resultingOwnership = _out204;
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
      DAST._IExpression _source81 = e;
      bool unmatched81 = true;
      if (unmatched81) {
        if (_source81.is_Literal) {
          DAST._ILiteral _h170 = _source81.dtor_Literal_a0;
          if (_h170.is_BoolLiteral) {
            bool _1707_b = _h170.dtor_BoolLiteral_a0;
            unmatched81 = false;
            {
              RAST._IExpr _out205;
              DCOMP._IOwnership _out206;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1707_b), expectedOwnership, out _out205, out _out206);
              r = _out205;
              resultingOwnership = _out206;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched81) {
        if (_source81.is_Literal) {
          DAST._ILiteral _h171 = _source81.dtor_Literal_a0;
          if (_h171.is_IntLiteral) {
            Dafny.ISequence<Dafny.Rune> _1708_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1709_t = _h171.dtor_IntLiteral_a1;
            unmatched81 = false;
            {
              DAST._IType _source82 = _1709_t;
              bool unmatched82 = true;
              if (unmatched82) {
                if (_source82.is_Primitive) {
                  DAST._IPrimitive _h70 = _source82.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched82 = false;
                    {
                      if ((new BigInteger((_1708_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1708_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1708_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched82) {
                DAST._IType _1710_o = _source82;
                unmatched82 = false;
                {
                  RAST._IType _1711_genType;
                  RAST._IType _out207;
                  _out207 = (this).GenType(_1710_o, DCOMP.GenTypeContext.@default());
                  _1711_genType = _out207;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1708_i), _1711_genType);
                }
              }
              RAST._IExpr _out208;
              DCOMP._IOwnership _out209;
              (this).FromOwned(r, expectedOwnership, out _out208, out _out209);
              r = _out208;
              resultingOwnership = _out209;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              return ;
            }
          }
        }
      }
      if (unmatched81) {
        if (_source81.is_Literal) {
          DAST._ILiteral _h172 = _source81.dtor_Literal_a0;
          if (_h172.is_DecLiteral) {
            Dafny.ISequence<Dafny.Rune> _1712_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1713_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1714_t = _h172.dtor_DecLiteral_a2;
            unmatched81 = false;
            {
              DAST._IType _source83 = _1714_t;
              bool unmatched83 = true;
              if (unmatched83) {
                if (_source83.is_Primitive) {
                  DAST._IPrimitive _h71 = _source83.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched83 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1712_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1713_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched83) {
                DAST._IType _1715_o = _source83;
                unmatched83 = false;
                {
                  RAST._IType _1716_genType;
                  RAST._IType _out210;
                  _out210 = (this).GenType(_1715_o, DCOMP.GenTypeContext.@default());
                  _1716_genType = _out210;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1712_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1713_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1716_genType);
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
      if (unmatched81) {
        if (_source81.is_Literal) {
          DAST._ILiteral _h173 = _source81.dtor_Literal_a0;
          if (_h173.is_StringLiteral) {
            Dafny.ISequence<Dafny.Rune> _1717_l = _h173.dtor_StringLiteral_a0;
            bool _1718_verbatim = _h173.dtor_verbatim;
            unmatched81 = false;
            {
              if (_1718_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1717_l, false, _1718_verbatim));
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
      if (unmatched81) {
        if (_source81.is_Literal) {
          DAST._ILiteral _h174 = _source81.dtor_Literal_a0;
          if (_h174.is_CharLiteralUTF16) {
            BigInteger _1719_c = _h174.dtor_CharLiteralUTF16_a0;
            unmatched81 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1719_c));
              r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
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
      if (unmatched81) {
        if (_source81.is_Literal) {
          DAST._ILiteral _h175 = _source81.dtor_Literal_a0;
          if (_h175.is_CharLiteral) {
            Dafny.Rune _1720_c = _h175.dtor_CharLiteral_a0;
            unmatched81 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1720_c).Value)));
              if (!((this).UnicodeChars)) {
                r = RAST.Expr.create_TypeAscription(r, RAST.Type.create_U16());
              } else {
                r = (((((((RAST.__default.@global).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("primitive"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_u32"))).Apply1(r)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unwrap"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(r);
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
      if (unmatched81) {
        DAST._ILiteral _h176 = _source81.dtor_Literal_a0;
        DAST._IType _1721_tpe = _h176.dtor_Null_a0;
        unmatched81 = false;
        {
          RAST._IType _1722_tpeGen;
          RAST._IType _out219;
          _out219 = (this).GenType(_1721_tpe, DCOMP.GenTypeContext.@default());
          _1722_tpeGen = _out219;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"));
          } else {
            r = RAST.Expr.create_TypeAscription(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1722_tpeGen);
          }
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
    public void GenExprBinary(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs53 = e;
      DAST._IBinOp _1723_op = _let_tmp_rhs53.dtor_op;
      DAST._IExpression _1724_lExpr = _let_tmp_rhs53.dtor_left;
      DAST._IExpression _1725_rExpr = _let_tmp_rhs53.dtor_right;
      DAST.Format._IBinaryOpFormat _1726_format = _let_tmp_rhs53.dtor_format2;
      bool _1727_becomesLeftCallsRight;
      _1727_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source84 = _1723_op;
        bool unmatched84 = true;
        if (unmatched84) {
          bool disjunctiveMatch14 = false;
          if (_source84.is_SetMerge) {
            disjunctiveMatch14 = true;
          }
          if (_source84.is_SetSubtraction) {
            disjunctiveMatch14 = true;
          }
          if (_source84.is_SetIntersection) {
            disjunctiveMatch14 = true;
          }
          if (_source84.is_SetDisjoint) {
            disjunctiveMatch14 = true;
          }
          if (_source84.is_MapMerge) {
            disjunctiveMatch14 = true;
          }
          if (_source84.is_MapSubtraction) {
            disjunctiveMatch14 = true;
          }
          if (_source84.is_MultisetMerge) {
            disjunctiveMatch14 = true;
          }
          if (_source84.is_MultisetSubtraction) {
            disjunctiveMatch14 = true;
          }
          if (_source84.is_MultisetIntersection) {
            disjunctiveMatch14 = true;
          }
          if (_source84.is_MultisetDisjoint) {
            disjunctiveMatch14 = true;
          }
          if (_source84.is_Concat) {
            disjunctiveMatch14 = true;
          }
          if (disjunctiveMatch14) {
            unmatched84 = false;
            return true;
          }
        }
        if (unmatched84) {
          DAST._IBinOp _1728___v109 = _source84;
          unmatched84 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1729_becomesRightCallsLeft;
      _1729_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source85 = _1723_op;
        bool unmatched85 = true;
        if (unmatched85) {
          if (_source85.is_In) {
            unmatched85 = false;
            return true;
          }
        }
        if (unmatched85) {
          DAST._IBinOp _1730___v110 = _source85;
          unmatched85 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1731_becomesCallLeftRight;
      _1731_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source86 = _1723_op;
        bool unmatched86 = true;
        if (unmatched86) {
          if (_source86.is_Eq) {
            bool referential0 = _source86.dtor_referential;
            if ((referential0) == (true)) {
              unmatched86 = false;
              return false;
            }
          }
        }
        if (unmatched86) {
          if (_source86.is_SetMerge) {
            unmatched86 = false;
            return true;
          }
        }
        if (unmatched86) {
          if (_source86.is_SetSubtraction) {
            unmatched86 = false;
            return true;
          }
        }
        if (unmatched86) {
          if (_source86.is_SetIntersection) {
            unmatched86 = false;
            return true;
          }
        }
        if (unmatched86) {
          if (_source86.is_SetDisjoint) {
            unmatched86 = false;
            return true;
          }
        }
        if (unmatched86) {
          if (_source86.is_MapMerge) {
            unmatched86 = false;
            return true;
          }
        }
        if (unmatched86) {
          if (_source86.is_MapSubtraction) {
            unmatched86 = false;
            return true;
          }
        }
        if (unmatched86) {
          if (_source86.is_MultisetMerge) {
            unmatched86 = false;
            return true;
          }
        }
        if (unmatched86) {
          if (_source86.is_MultisetSubtraction) {
            unmatched86 = false;
            return true;
          }
        }
        if (unmatched86) {
          if (_source86.is_MultisetIntersection) {
            unmatched86 = false;
            return true;
          }
        }
        if (unmatched86) {
          if (_source86.is_MultisetDisjoint) {
            unmatched86 = false;
            return true;
          }
        }
        if (unmatched86) {
          if (_source86.is_Concat) {
            unmatched86 = false;
            return true;
          }
        }
        if (unmatched86) {
          DAST._IBinOp _1732___v111 = _source86;
          unmatched86 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1733_expectedLeftOwnership;
      _1733_expectedLeftOwnership = ((_1727_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1729_becomesRightCallsLeft) || (_1731_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1734_expectedRightOwnership;
      _1734_expectedRightOwnership = (((_1727_becomesLeftCallsRight) || (_1731_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1729_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1735_left;
      DCOMP._IOwnership _1736___v112;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1737_recIdentsL;
      RAST._IExpr _out222;
      DCOMP._IOwnership _out223;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out224;
      (this).GenExpr(_1724_lExpr, selfIdent, env, _1733_expectedLeftOwnership, out _out222, out _out223, out _out224);
      _1735_left = _out222;
      _1736___v112 = _out223;
      _1737_recIdentsL = _out224;
      RAST._IExpr _1738_right;
      DCOMP._IOwnership _1739___v113;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1740_recIdentsR;
      RAST._IExpr _out225;
      DCOMP._IOwnership _out226;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
      (this).GenExpr(_1725_rExpr, selfIdent, env, _1734_expectedRightOwnership, out _out225, out _out226, out _out227);
      _1738_right = _out225;
      _1739___v113 = _out226;
      _1740_recIdentsR = _out227;
      DAST._IBinOp _source87 = _1723_op;
      bool unmatched87 = true;
      if (unmatched87) {
        if (_source87.is_In) {
          unmatched87 = false;
          {
            r = ((_1738_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1735_left);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SeqProperPrefix) {
          unmatched87 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1735_left, _1738_right, _1726_format);
        }
      }
      if (unmatched87) {
        if (_source87.is_SeqPrefix) {
          unmatched87 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1735_left, _1738_right, _1726_format);
        }
      }
      if (unmatched87) {
        if (_source87.is_SetMerge) {
          unmatched87 = false;
          {
            r = ((_1735_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1738_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SetSubtraction) {
          unmatched87 = false;
          {
            r = ((_1735_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1738_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SetIntersection) {
          unmatched87 = false;
          {
            r = ((_1735_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1738_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Subset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1735_left, _1738_right, _1726_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_ProperSubset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1735_left, _1738_right, _1726_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SetDisjoint) {
          unmatched87 = false;
          {
            r = ((_1735_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1738_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MapMerge) {
          unmatched87 = false;
          {
            r = ((_1735_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1738_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MapSubtraction) {
          unmatched87 = false;
          {
            r = ((_1735_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1738_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetMerge) {
          unmatched87 = false;
          {
            r = ((_1735_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1738_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetSubtraction) {
          unmatched87 = false;
          {
            r = ((_1735_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1738_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetIntersection) {
          unmatched87 = false;
          {
            r = ((_1735_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1738_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Submultiset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1735_left, _1738_right, _1726_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_ProperSubmultiset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1735_left, _1738_right, _1726_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetDisjoint) {
          unmatched87 = false;
          {
            r = ((_1735_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1738_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Concat) {
          unmatched87 = false;
          {
            r = ((_1735_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1738_right);
          }
        }
      }
      if (unmatched87) {
        DAST._IBinOp _1741___v114 = _source87;
        unmatched87 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1723_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1723_op), _1735_left, _1738_right, _1726_format);
          } else {
            DAST._IBinOp _source88 = _1723_op;
            bool unmatched88 = true;
            if (unmatched88) {
              if (_source88.is_Eq) {
                bool _1742_referential = _source88.dtor_referential;
                unmatched88 = false;
                {
                  if (_1742_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1735_left, _1738_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1725_rExpr).is_SeqValue) && ((new BigInteger(((_1725_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1735_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1724_lExpr).is_SeqValue) && ((new BigInteger(((_1724_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1738_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1735_left, _1738_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched88) {
              if (_source88.is_EuclidianDiv) {
                unmatched88 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1735_left, _1738_right));
                }
              }
            }
            if (unmatched88) {
              if (_source88.is_EuclidianMod) {
                unmatched88 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1735_left, _1738_right));
                }
              }
            }
            if (unmatched88) {
              Dafny.ISequence<Dafny.Rune> _1743_op = _source88.dtor_Passthrough_a0;
              unmatched88 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1743_op, _1735_left, _1738_right, _1726_format);
              }
            }
          }
        }
      }
      RAST._IExpr _out228;
      DCOMP._IOwnership _out229;
      (this).FromOwned(r, expectedOwnership, out _out228, out _out229);
      r = _out228;
      resultingOwnership = _out229;
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1737_recIdentsL, _1740_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _1744_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _1745_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _1746_toTpe = _let_tmp_rhs54.dtor_typ;
      DAST._IType _let_tmp_rhs55 = _1746_toTpe;
      DAST._IResolvedType _let_tmp_rhs56 = _let_tmp_rhs55.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1747_path = _let_tmp_rhs56.dtor_path;
      Dafny.ISequence<DAST._IType> _1748_typeArgs = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs57 = _let_tmp_rhs56.dtor_kind;
      DAST._IType _1749_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1750_range = _let_tmp_rhs57.dtor_range;
      bool _1751_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1752___v115 = _let_tmp_rhs56.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1753___v116 = _let_tmp_rhs56.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1754___v117 = _let_tmp_rhs56.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1755_nativeToType;
      _1755_nativeToType = DCOMP.COMP.NewtypeToRustType(_1749_b, _1750_range);
      if (object.Equals(_1745_fromTpe, _1749_b)) {
        RAST._IExpr _1756_recursiveGen;
        DCOMP._IOwnership _1757_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1758_recIdents;
        RAST._IExpr _out230;
        DCOMP._IOwnership _out231;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out232;
        (this).GenExpr(_1744_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out230, out _out231, out _out232);
        _1756_recursiveGen = _out230;
        _1757_recOwned = _out231;
        _1758_recIdents = _out232;
        readIdents = _1758_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source89 = _1755_nativeToType;
        bool unmatched89 = true;
        if (unmatched89) {
          if (_source89.is_Some) {
            RAST._IType _1759_v = _source89.dtor_value;
            unmatched89 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1756_recursiveGen, RAST.Expr.create_ExprFromType(_1759_v)));
            RAST._IExpr _out233;
            DCOMP._IOwnership _out234;
            (this).FromOwned(r, expectedOwnership, out _out233, out _out234);
            r = _out233;
            resultingOwnership = _out234;
          }
        }
        if (unmatched89) {
          unmatched89 = false;
          if (_1751_erase) {
            r = _1756_recursiveGen;
          } else {
            RAST._IType _1760_rhsType;
            RAST._IType _out235;
            _out235 = (this).GenType(_1746_toTpe, DCOMP.GenTypeContext.InBinding());
            _1760_rhsType = _out235;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1760_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1756_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out236;
          DCOMP._IOwnership _out237;
          (this).FromOwnership(r, _1757_recOwned, expectedOwnership, out _out236, out _out237);
          r = _out236;
          resultingOwnership = _out237;
        }
      } else {
        if ((_1755_nativeToType).is_Some) {
          DAST._IType _source90 = _1745_fromTpe;
          bool unmatched90 = true;
          if (unmatched90) {
            if (_source90.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source90.dtor_resolved;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1761___v118 = resolved1.dtor_path;
              Dafny.ISequence<DAST._IType> _1762___v119 = resolved1.dtor_typeArgs;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1763_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1764_range0 = kind1.dtor_range;
                bool _1765_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1766_attributes0 = resolved1.dtor_attributes;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1767___v120 = resolved1.dtor_properMethods;
                Dafny.ISequence<DAST._IType> _1768___v121 = resolved1.dtor_extendedTypes;
                unmatched90 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1769_nativeFromType;
                  _1769_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1763_b0, _1764_range0);
                  if ((_1769_nativeFromType).is_Some) {
                    RAST._IExpr _1770_recursiveGen;
                    DCOMP._IOwnership _1771_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1772_recIdents;
                    RAST._IExpr _out238;
                    DCOMP._IOwnership _out239;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out240;
                    (this).GenExpr(_1744_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out238, out _out239, out _out240);
                    _1770_recursiveGen = _out238;
                    _1771_recOwned = _out239;
                    _1772_recIdents = _out240;
                    RAST._IExpr _out241;
                    DCOMP._IOwnership _out242;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1770_recursiveGen, (_1755_nativeToType).dtor_value), _1771_recOwned, expectedOwnership, out _out241, out _out242);
                    r = _out241;
                    resultingOwnership = _out242;
                    readIdents = _1772_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched90) {
            DAST._IType _1773___v122 = _source90;
            unmatched90 = false;
          }
          if (object.Equals(_1745_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1774_recursiveGen;
            DCOMP._IOwnership _1775_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1776_recIdents;
            RAST._IExpr _out243;
            DCOMP._IOwnership _out244;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out245;
            (this).GenExpr(_1744_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out243, out _out244, out _out245);
            _1774_recursiveGen = _out243;
            _1775_recOwned = _out244;
            _1776_recIdents = _out245;
            RAST._IExpr _out246;
            DCOMP._IOwnership _out247;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1774_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1755_nativeToType).dtor_value), _1775_recOwned, expectedOwnership, out _out246, out _out247);
            r = _out246;
            resultingOwnership = _out247;
            readIdents = _1776_recIdents;
            return ;
          }
        }
        RAST._IExpr _out248;
        DCOMP._IOwnership _out249;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1744_expr, _1745_fromTpe, _1749_b), _1749_b, _1746_toTpe), selfIdent, env, expectedOwnership, out _out248, out _out249, out _out250);
        r = _out248;
        resultingOwnership = _out249;
        readIdents = _out250;
      }
    }
    public void GenExprConvertFromNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs58 = e;
      DAST._IExpression _1777_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1778_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1779_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _1778_fromTpe;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1780___v123 = _let_tmp_rhs60.dtor_path;
      Dafny.ISequence<DAST._IType> _1781___v124 = _let_tmp_rhs60.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs61 = _let_tmp_rhs60.dtor_kind;
      DAST._IType _1782_b = _let_tmp_rhs61.dtor_baseType;
      DAST._INewtypeRange _1783_range = _let_tmp_rhs61.dtor_range;
      bool _1784_erase = _let_tmp_rhs61.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1785_attributes = _let_tmp_rhs60.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1786___v125 = _let_tmp_rhs60.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1787___v126 = _let_tmp_rhs60.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1788_nativeFromType;
      _1788_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1782_b, _1783_range);
      if (object.Equals(_1782_b, _1779_toTpe)) {
        RAST._IExpr _1789_recursiveGen;
        DCOMP._IOwnership _1790_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1791_recIdents;
        RAST._IExpr _out251;
        DCOMP._IOwnership _out252;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
        (this).GenExpr(_1777_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out251, out _out252, out _out253);
        _1789_recursiveGen = _out251;
        _1790_recOwned = _out252;
        _1791_recIdents = _out253;
        readIdents = _1791_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source91 = _1788_nativeFromType;
        bool unmatched91 = true;
        if (unmatched91) {
          if (_source91.is_Some) {
            RAST._IType _1792_v = _source91.dtor_value;
            unmatched91 = false;
            RAST._IType _1793_toTpeRust;
            RAST._IType _out254;
            _out254 = (this).GenType(_1779_toTpe, DCOMP.GenTypeContext.@default());
            _1793_toTpeRust = _out254;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1793_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1789_recursiveGen));
            RAST._IExpr _out255;
            DCOMP._IOwnership _out256;
            (this).FromOwned(r, expectedOwnership, out _out255, out _out256);
            r = _out255;
            resultingOwnership = _out256;
          }
        }
        if (unmatched91) {
          unmatched91 = false;
          if (_1784_erase) {
            r = _1789_recursiveGen;
          } else {
            r = (_1789_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out257;
          DCOMP._IOwnership _out258;
          (this).FromOwnership(r, _1790_recOwned, expectedOwnership, out _out257, out _out258);
          r = _out257;
          resultingOwnership = _out258;
        }
      } else {
        if ((_1788_nativeFromType).is_Some) {
          if (object.Equals(_1779_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1794_recursiveGen;
            DCOMP._IOwnership _1795_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1796_recIdents;
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out261;
            (this).GenExpr(_1777_expr, selfIdent, env, expectedOwnership, out _out259, out _out260, out _out261);
            _1794_recursiveGen = _out259;
            _1795_recOwned = _out260;
            _1796_recIdents = _out261;
            RAST._IExpr _out262;
            DCOMP._IOwnership _out263;
            (this).FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1794_recursiveGen, (this).DafnyCharUnderlying)), _1795_recOwned, expectedOwnership, out _out262, out _out263);
            r = _out262;
            resultingOwnership = _out263;
            readIdents = _1796_recIdents;
            return ;
          }
        }
        RAST._IExpr _out264;
        DCOMP._IOwnership _out265;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1777_expr, _1778_fromTpe, _1782_b), _1782_b, _1779_toTpe), selfIdent, env, expectedOwnership, out _out264, out _out265, out _out266);
        r = _out264;
        resultingOwnership = _out265;
        readIdents = _out266;
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
        Std.Wrappers._IResult<__T, __E> _1797_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1797_valueOrError0).IsFailure()) {
          return (_1797_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1798_head = (_1797_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1799_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1799_valueOrError1).IsFailure()) {
            return (_1799_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1800_tail = (_1799_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1798_head), _1800_tail));
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
          RAST._IType _1801_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1802_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel((this).upcast)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1801_fromTpeUnderlying, _1802_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1803_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1803_valueOrError0).IsFailure()) {
          return (_1803_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1804_lambda = (_1803_valueOrError0).Extract();
          if ((fromType).is_Arrow) {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(_1804_lambda);
          } else {
            return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).Apply1(_1804_lambda));
          }
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1805_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim12 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr12 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
          for (int i12 = 0; i12 < dim12; i12++) {
            var _1806_i = (BigInteger) i12;
            arr12[(int)(_1806_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_1806_i), ((fromTpe).dtor_arguments).Select(_1806_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_1806_i), ((toTpe).dtor_arguments).Select(_1806_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr12);
        }))());
        if ((_1805_valueOrError1).IsFailure()) {
          return (_1805_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1807_lambdas = (_1805_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim13 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr13 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
  for (int i13 = 0; i13 < dim13; i13++) {
    var _1808_i = (BigInteger) i13;
    arr13[(int)(_1808_i)] = ((fromTpe).dtor_arguments).Select(_1808_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr13);
}))())).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1807_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1809_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1810_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1811_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1812_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1813_valueOrError2 = (this).UpcastConversionLambda(_1811_newFromType, _1809_newFromTpe, _1812_newToType, _1810_newToTpe, typeParams);
        if ((_1813_valueOrError2).IsFailure()) {
          return (_1813_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1814_coerceArg = (_1813_valueOrError2).Extract();
          RAST._IExpr _1815_collectionType = (RAST.__default.dafny__runtime).MSel(((fromTpe).dtor_baseName).dtor_name);
          RAST._IExpr _1816_baseType = (((((fromTpe).dtor_baseName).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? ((_1815_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((fromTpe).dtor_arguments).Select(BigInteger.Zero), _1809_newFromTpe))) : ((_1815_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1809_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1816_baseType).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1814_coerceArg));
        }
      } else if ((((((((((fromTpe).is_DynType) && (((fromTpe).dtor_underlying).is_FnType)) && ((toTpe).is_DynType)) && (((toTpe).dtor_underlying).is_FnType)) && ((((fromTpe).dtor_underlying).dtor_arguments).Equals(((toTpe).dtor_underlying).dtor_arguments))) && ((fromType).is_Arrow)) && ((toType).is_Arrow)) && ((new BigInteger((((fromTpe).dtor_underlying).dtor_arguments).Count)) == (BigInteger.One))) && (((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).is_Borrowed)) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1817_valueOrError3 = (this).UpcastConversionLambda((fromType).dtor_result, ((fromTpe).dtor_underlying).dtor_returnType, (toType).dtor_result, ((toTpe).dtor_underlying).dtor_returnType, typeParams);
        if ((_1817_valueOrError3).IsFailure()) {
          return (_1817_valueOrError3).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1818_lambda = (_1817_valueOrError3).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fn1_coerce"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((((fromTpe).dtor_underlying).dtor_arguments).Select(BigInteger.Zero)).dtor_underlying, ((fromTpe).dtor_underlying).dtor_returnType, ((toTpe).dtor_underlying).dtor_returnType))).Apply1(_1818_lambda));
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
      DAST._IExpression _let_tmp_rhs62 = e;
      DAST._IExpression _1819_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _1820_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _1821_toTpe = _let_tmp_rhs62.dtor_typ;
      RAST._IType _1822_fromTpeGen;
      RAST._IType _out267;
      _out267 = (this).GenType(_1820_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1822_fromTpeGen = _out267;
      RAST._IType _1823_toTpeGen;
      RAST._IType _out268;
      _out268 = (this).GenType(_1821_toTpe, DCOMP.GenTypeContext.InBinding());
      _1823_toTpeGen = _out268;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1824_upcastConverter;
      _1824_upcastConverter = (this).UpcastConversionLambda(_1820_fromTpe, _1822_fromTpeGen, _1821_toTpe, _1823_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1824_upcastConverter).is_Success) {
        RAST._IExpr _1825_conversionLambda;
        _1825_conversionLambda = (_1824_upcastConverter).dtor_value;
        RAST._IExpr _1826_recursiveGen;
        DCOMP._IOwnership _1827_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1828_recIdents;
        RAST._IExpr _out269;
        DCOMP._IOwnership _out270;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
        (this).GenExpr(_1819_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out269, out _out270, out _out271);
        _1826_recursiveGen = _out269;
        _1827_recOwned = _out270;
        _1828_recIdents = _out271;
        readIdents = _1828_recIdents;
        r = (_1825_conversionLambda).Apply1(_1826_recursiveGen);
        RAST._IExpr _out272;
        DCOMP._IOwnership _out273;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out272, out _out273);
        r = _out272;
        resultingOwnership = _out273;
      } else if ((this).IsDowncastConversion(_1822_fromTpeGen, _1823_toTpeGen)) {
        RAST._IExpr _1829_recursiveGen;
        DCOMP._IOwnership _1830_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1831_recIdents;
        RAST._IExpr _out274;
        DCOMP._IOwnership _out275;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out276;
        (this).GenExpr(_1819_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out274, out _out275, out _out276);
        _1829_recursiveGen = _out274;
        _1830_recOwned = _out275;
        _1831_recIdents = _out276;
        readIdents = _1831_recIdents;
        _1823_toTpeGen = (_1823_toTpeGen).ObjectOrPointerUnderlying();
        r = ((RAST.__default.dafny__runtime).MSel((this).downcast)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1829_recursiveGen, RAST.Expr.create_ExprFromType(_1823_toTpeGen)));
        RAST._IExpr _out277;
        DCOMP._IOwnership _out278;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out277, out _out278);
        r = _out277;
        resultingOwnership = _out278;
      } else {
        RAST._IExpr _1832_recursiveGen;
        DCOMP._IOwnership _1833_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1834_recIdents;
        RAST._IExpr _out279;
        DCOMP._IOwnership _out280;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out281;
        (this).GenExpr(_1819_expr, selfIdent, env, expectedOwnership, out _out279, out _out280, out _out281);
        _1832_recursiveGen = _out279;
        _1833_recOwned = _out280;
        _1834_recIdents = _out281;
        readIdents = _1834_recIdents;
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _let_tmp_rhs63 = _1824_upcastConverter;
        _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>> _let_tmp_rhs64 = _let_tmp_rhs63.dtor_error;
        DAST._IType _1835_fromType = _let_tmp_rhs64.dtor__0;
        RAST._IType _1836_fromTpeGen = _let_tmp_rhs64.dtor__1;
        DAST._IType _1837_toType = _let_tmp_rhs64.dtor__2;
        RAST._IType _1838_toTpeGen = _let_tmp_rhs64.dtor__3;
        Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1839_m = _let_tmp_rhs64.dtor__4;
        Dafny.ISequence<Dafny.Rune> _1840_msg;
        _1840_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1836_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1838_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1840_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1832_recursiveGen)._ToString(DCOMP.__default.IND), _1840_msg));
        RAST._IExpr _out282;
        DCOMP._IOwnership _out283;
        (this).FromOwnership(r, _1833_recOwned, expectedOwnership, out _out282, out _out283);
        r = _out282;
        resultingOwnership = _out283;
      }
    }
    public void GenExprConvert(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs65 = e;
      DAST._IExpression _1841_expr = _let_tmp_rhs65.dtor_value;
      DAST._IType _1842_fromTpe = _let_tmp_rhs65.dtor_from;
      DAST._IType _1843_toTpe = _let_tmp_rhs65.dtor_typ;
      if (object.Equals(_1842_fromTpe, _1843_toTpe)) {
        RAST._IExpr _1844_recursiveGen;
        DCOMP._IOwnership _1845_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1846_recIdents;
        RAST._IExpr _out284;
        DCOMP._IOwnership _out285;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
        (this).GenExpr(_1841_expr, selfIdent, env, expectedOwnership, out _out284, out _out285, out _out286);
        _1844_recursiveGen = _out284;
        _1845_recOwned = _out285;
        _1846_recIdents = _out286;
        r = _1844_recursiveGen;
        RAST._IExpr _out287;
        DCOMP._IOwnership _out288;
        (this).FromOwnership(r, _1845_recOwned, expectedOwnership, out _out287, out _out288);
        r = _out287;
        resultingOwnership = _out288;
        readIdents = _1846_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source92 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1842_fromTpe, _1843_toTpe);
        bool unmatched92 = true;
        if (unmatched92) {
          DAST._IType _1847___v127 = _source92.dtor__0;
          DAST._IType _10 = _source92.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1848___v128 = resolved2.dtor_path;
            Dafny.ISequence<DAST._IType> _1849___v129 = resolved2.dtor_typeArgs;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1850_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1851_range = kind2.dtor_range;
              bool _1852_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1853_attributes = resolved2.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1854___v130 = resolved2.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1855___v131 = resolved2.dtor_extendedTypes;
              unmatched92 = false;
              {
                RAST._IExpr _out289;
                DCOMP._IOwnership _out290;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out291;
                (this).GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership, out _out289, out _out290, out _out291);
                r = _out289;
                resultingOwnership = _out290;
                readIdents = _out291;
              }
            }
          }
        }
        if (unmatched92) {
          DAST._IType _00 = _source92.dtor__0;
          if (_00.is_UserDefined) {
            DAST._IResolvedType resolved3 = _00.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1856___v132 = resolved3.dtor_path;
            Dafny.ISequence<DAST._IType> _1857___v133 = resolved3.dtor_typeArgs;
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1858_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1859_range = kind3.dtor_range;
              bool _1860_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1861_attributes = resolved3.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1862___v134 = resolved3.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1863___v135 = resolved3.dtor_extendedTypes;
              DAST._IType _1864___v136 = _source92.dtor__1;
              unmatched92 = false;
              {
                RAST._IExpr _out292;
                DCOMP._IOwnership _out293;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out294;
                (this).GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership, out _out292, out _out293, out _out294);
                r = _out292;
                resultingOwnership = _out293;
                readIdents = _out294;
              }
            }
          }
        }
        if (unmatched92) {
          DAST._IType _01 = _source92.dtor__0;
          if (_01.is_Primitive) {
            DAST._IPrimitive _h72 = _01.dtor_Primitive_a0;
            if (_h72.is_Int) {
              DAST._IType _11 = _source92.dtor__1;
              if (_11.is_Primitive) {
                DAST._IPrimitive _h73 = _11.dtor_Primitive_a0;
                if (_h73.is_Real) {
                  unmatched92 = false;
                  {
                    RAST._IExpr _1865_recursiveGen;
                    DCOMP._IOwnership _1866___v137;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1867_recIdents;
                    RAST._IExpr _out295;
                    DCOMP._IOwnership _out296;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out297;
                    (this).GenExpr(_1841_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out295, out _out296, out _out297);
                    _1865_recursiveGen = _out295;
                    _1866___v137 = _out296;
                    _1867_recIdents = _out297;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1865_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out298;
                    DCOMP._IOwnership _out299;
                    (this).FromOwned(r, expectedOwnership, out _out298, out _out299);
                    r = _out298;
                    resultingOwnership = _out299;
                    readIdents = _1867_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched92) {
          DAST._IType _02 = _source92.dtor__0;
          if (_02.is_Primitive) {
            DAST._IPrimitive _h74 = _02.dtor_Primitive_a0;
            if (_h74.is_Real) {
              DAST._IType _12 = _source92.dtor__1;
              if (_12.is_Primitive) {
                DAST._IPrimitive _h75 = _12.dtor_Primitive_a0;
                if (_h75.is_Int) {
                  unmatched92 = false;
                  {
                    RAST._IExpr _1868_recursiveGen;
                    DCOMP._IOwnership _1869___v138;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1870_recIdents;
                    RAST._IExpr _out300;
                    DCOMP._IOwnership _out301;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out302;
                    (this).GenExpr(_1841_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out300, out _out301, out _out302);
                    _1868_recursiveGen = _out300;
                    _1869___v138 = _out301;
                    _1870_recIdents = _out302;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1868_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out303;
                    DCOMP._IOwnership _out304;
                    (this).FromOwned(r, expectedOwnership, out _out303, out _out304);
                    r = _out303;
                    resultingOwnership = _out304;
                    readIdents = _1870_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched92) {
          DAST._IType _03 = _source92.dtor__0;
          if (_03.is_Primitive) {
            DAST._IPrimitive _h76 = _03.dtor_Primitive_a0;
            if (_h76.is_Int) {
              DAST._IType _13 = _source92.dtor__1;
              if (_13.is_Passthrough) {
                Dafny.ISequence<Dafny.Rune> _1871___v139 = _13.dtor_Passthrough_a0;
                unmatched92 = false;
                {
                  RAST._IType _1872_rhsType;
                  RAST._IType _out305;
                  _out305 = (this).GenType(_1843_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1872_rhsType = _out305;
                  RAST._IExpr _1873_recursiveGen;
                  DCOMP._IOwnership _1874___v140;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1875_recIdents;
                  RAST._IExpr _out306;
                  DCOMP._IOwnership _out307;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out308;
                  (this).GenExpr(_1841_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out306, out _out307, out _out308);
                  _1873_recursiveGen = _out306;
                  _1874___v140 = _out307;
                  _1875_recIdents = _out308;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1872_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1873_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out309;
                  DCOMP._IOwnership _out310;
                  (this).FromOwned(r, expectedOwnership, out _out309, out _out310);
                  r = _out309;
                  resultingOwnership = _out310;
                  readIdents = _1875_recIdents;
                }
              }
            }
          }
        }
        if (unmatched92) {
          DAST._IType _04 = _source92.dtor__0;
          if (_04.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1876___v141 = _04.dtor_Passthrough_a0;
            DAST._IType _14 = _source92.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h77 = _14.dtor_Primitive_a0;
              if (_h77.is_Int) {
                unmatched92 = false;
                {
                  RAST._IType _1877_rhsType;
                  RAST._IType _out311;
                  _out311 = (this).GenType(_1842_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1877_rhsType = _out311;
                  RAST._IExpr _1878_recursiveGen;
                  DCOMP._IOwnership _1879___v142;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1880_recIdents;
                  RAST._IExpr _out312;
                  DCOMP._IOwnership _out313;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out314;
                  (this).GenExpr(_1841_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out312, out _out313, out _out314);
                  _1878_recursiveGen = _out312;
                  _1879___v142 = _out313;
                  _1880_recIdents = _out314;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1878_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out315;
                  DCOMP._IOwnership _out316;
                  (this).FromOwned(r, expectedOwnership, out _out315, out _out316);
                  r = _out315;
                  resultingOwnership = _out316;
                  readIdents = _1880_recIdents;
                }
              }
            }
          }
        }
        if (unmatched92) {
          DAST._IType _05 = _source92.dtor__0;
          if (_05.is_Primitive) {
            DAST._IPrimitive _h78 = _05.dtor_Primitive_a0;
            if (_h78.is_Int) {
              DAST._IType _15 = _source92.dtor__1;
              if (_15.is_Primitive) {
                DAST._IPrimitive _h79 = _15.dtor_Primitive_a0;
                if (_h79.is_Char) {
                  unmatched92 = false;
                  {
                    RAST._IType _1881_rhsType;
                    RAST._IType _out317;
                    _out317 = (this).GenType(_1843_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1881_rhsType = _out317;
                    RAST._IExpr _1882_recursiveGen;
                    DCOMP._IOwnership _1883___v143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1884_recIdents;
                    RAST._IExpr _out318;
                    DCOMP._IOwnership _out319;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
                    (this).GenExpr(_1841_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out318, out _out319, out _out320);
                    _1882_recursiveGen = _out318;
                    _1883___v143 = _out319;
                    _1884_recIdents = _out320;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1882_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out321;
                    DCOMP._IOwnership _out322;
                    (this).FromOwned(r, expectedOwnership, out _out321, out _out322);
                    r = _out321;
                    resultingOwnership = _out322;
                    readIdents = _1884_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched92) {
          DAST._IType _06 = _source92.dtor__0;
          if (_06.is_Primitive) {
            DAST._IPrimitive _h710 = _06.dtor_Primitive_a0;
            if (_h710.is_Char) {
              DAST._IType _16 = _source92.dtor__1;
              if (_16.is_Primitive) {
                DAST._IPrimitive _h711 = _16.dtor_Primitive_a0;
                if (_h711.is_Int) {
                  unmatched92 = false;
                  {
                    RAST._IType _1885_rhsType;
                    RAST._IType _out323;
                    _out323 = (this).GenType(_1842_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1885_rhsType = _out323;
                    RAST._IExpr _1886_recursiveGen;
                    DCOMP._IOwnership _1887___v144;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1888_recIdents;
                    RAST._IExpr _out324;
                    DCOMP._IOwnership _out325;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
                    (this).GenExpr(_1841_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out324, out _out325, out _out326);
                    _1886_recursiveGen = _out324;
                    _1887___v144 = _out325;
                    _1888_recIdents = _out326;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1886_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out327;
                    DCOMP._IOwnership _out328;
                    (this).FromOwned(r, expectedOwnership, out _out327, out _out328);
                    r = _out327;
                    resultingOwnership = _out328;
                    readIdents = _1888_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched92) {
          DAST._IType _07 = _source92.dtor__0;
          if (_07.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1889___v145 = _07.dtor_Passthrough_a0;
            DAST._IType _17 = _source92.dtor__1;
            if (_17.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1890___v146 = _17.dtor_Passthrough_a0;
              unmatched92 = false;
              {
                RAST._IExpr _1891_recursiveGen;
                DCOMP._IOwnership _1892___v147;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1893_recIdents;
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExpr(_1841_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out329, out _out330, out _out331);
                _1891_recursiveGen = _out329;
                _1892___v147 = _out330;
                _1893_recIdents = _out331;
                RAST._IType _1894_toTpeGen;
                RAST._IType _out332;
                _out332 = (this).GenType(_1843_toTpe, DCOMP.GenTypeContext.InBinding());
                _1894_toTpeGen = _out332;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1891_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1894_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out333;
                DCOMP._IOwnership _out334;
                (this).FromOwned(r, expectedOwnership, out _out333, out _out334);
                r = _out333;
                resultingOwnership = _out334;
                readIdents = _1893_recIdents;
              }
            }
          }
        }
        if (unmatched92) {
          _System._ITuple2<DAST._IType, DAST._IType> _1895___v148 = _source92;
          unmatched92 = false;
          {
            RAST._IExpr _out335;
            DCOMP._IOwnership _out336;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out337;
            (this).GenExprConvertOther(e, selfIdent, env, expectedOwnership, out _out335, out _out336, out _out337);
            r = _out335;
            resultingOwnership = _out336;
            readIdents = _out337;
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
      Std.Wrappers._IOption<RAST._IType> _1896_tpe;
      _1896_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1897_placeboOpt;
      _1897_placeboOpt = (((_1896_tpe).is_Some) ? (((_1896_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1898_currentlyBorrowed;
      _1898_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1899_noNeedOfClone;
      _1899_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1897_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1898_currentlyBorrowed = false;
        _1899_noNeedOfClone = true;
        _1896_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1897_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_1898_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1896_tpe).is_Some) && (((_1896_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1900_needObjectFromRef;
        _1900_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source93 = (selfIdent).dtor_dafnyType;
          bool unmatched93 = true;
          if (unmatched93) {
            if (_source93.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source93.dtor_resolved;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1901___v149 = resolved4.dtor_path;
              Dafny.ISequence<DAST._IType> _1902___v150 = resolved4.dtor_typeArgs;
              DAST._IResolvedTypeBase _1903_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1904_attributes = resolved4.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1905___v151 = resolved4.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1906___v152 = resolved4.dtor_extendedTypes;
              unmatched93 = false;
              return ((_1903_base).is_Class) || ((_1903_base).is_Trait);
            }
          }
          if (unmatched93) {
            DAST._IType _1907___v153 = _source93;
            unmatched93 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_1900_needObjectFromRef) {
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1899_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1899_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1898_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1896_tpe).is_Some) && (((_1896_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1908_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1908_attributes).UniqueElements, false, (((_exists_var_1) => {
        DAST._IAttribute _1909_attribute = (DAST._IAttribute)_exists_var_1;
        return ((_1908_attributes).Contains(_1909_attribute)) && ((((_1909_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1909_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      for (BigInteger _1910_i = BigInteger.Zero; _1910_i < _hi36; _1910_i++) {
        DCOMP._IOwnership _1911_argOwnership;
        _1911_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if (((name).is_CallName) && ((_1910_i) < (new BigInteger((((name).dtor_signature)).Count)))) {
          RAST._IType _1912_tpe;
          RAST._IType _out338;
          _out338 = (this).GenType(((((name).dtor_signature)).Select(_1910_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1912_tpe = _out338;
          if ((_1912_tpe).CanReadWithoutClone()) {
            _1911_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1913_argExpr;
        DCOMP._IOwnership _1914___v154;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1915_argIdents;
        RAST._IExpr _out339;
        DCOMP._IOwnership _out340;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out341;
        (this).GenExpr((args).Select(_1910_i), selfIdent, env, _1911_argOwnership, out _out339, out _out340, out _out341);
        _1913_argExpr = _out339;
        _1914___v154 = _out340;
        _1915_argIdents = _out341;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1913_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1915_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi37 = new BigInteger((typeArgs).Count);
      for (BigInteger _1916_typeI = BigInteger.Zero; _1916_typeI < _hi37; _1916_typeI++) {
        RAST._IType _1917_typeExpr;
        RAST._IType _out342;
        _out342 = (this).GenType((typeArgs).Select(_1916_typeI), DCOMP.GenTypeContext.@default());
        _1917_typeExpr = _out342;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1917_typeExpr));
      }
      fullNameQualifier = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
        DAST._ICallName _source94 = name;
        bool unmatched94 = true;
        if (unmatched94) {
          if (_source94.is_CallName) {
            Dafny.ISequence<Dafny.Rune> _1918_nameIdent = _source94.dtor_name;
            Std.Wrappers._IOption<DAST._IType> onType1 = _source94.dtor_onType;
            if (onType1.is_Some) {
              DAST._IType value10 = onType1.dtor_value;
              if (value10.is_UserDefined) {
                DAST._IResolvedType _1919_resolvedType = value10.dtor_resolved;
                Std.Wrappers._IOption<DAST._IFormal> _1920___v155 = _source94.dtor_receiverArgs;
                Dafny.ISequence<DAST._IFormal> _1921___v156 = _source94.dtor_signature;
                unmatched94 = false;
                if ((((_1919_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_1922_resolvedType, _1923_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(((_1922_resolvedType).dtor_properMethods).UniqueElements, true, (((_forall_var_8) => {
                  Dafny.ISequence<Dafny.Rune> _1924_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                  return !(((_1922_resolvedType).dtor_properMethods).Contains(_1924_m)) || (!object.Equals((_1924_m), _1923_nameIdent));
                }))))(_1919_resolvedType, _1918_nameIdent))) {
                  return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_1919_resolvedType, (_1918_nameIdent)), _1919_resolvedType));
                } else {
                  return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
                }
              }
            }
          }
        }
        if (unmatched94) {
          DAST._ICallName _1925___v157 = _source94;
          unmatched94 = false;
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
      DAST._IExpression _source95 = e;
      bool unmatched95 = true;
      if (unmatched95) {
        if (_source95.is_Literal) {
          DAST._ILiteral _1926___v158 = _source95.dtor_Literal_a0;
          unmatched95 = false;
          RAST._IExpr _out343;
          DCOMP._IOwnership _out344;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out345;
          (this).GenExprLiteral(e, selfIdent, env, expectedOwnership, out _out343, out _out344, out _out345);
          r = _out343;
          resultingOwnership = _out344;
          readIdents = _out345;
        }
      }
      if (unmatched95) {
        if (_source95.is_Ident) {
          Dafny.ISequence<Dafny.Rune> _1927_name = _source95.dtor_Ident_a0;
          unmatched95 = false;
          {
            RAST._IExpr _out346;
            DCOMP._IOwnership _out347;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
            (this).GenIdent(DCOMP.__default.escapeName(_1927_name), selfIdent, env, expectedOwnership, out _out346, out _out347, out _out348);
            r = _out346;
            resultingOwnership = _out347;
            readIdents = _out348;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1928_path = _source95.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _1929_typeArgs = _source95.dtor_typeArgs;
          unmatched95 = false;
          {
            RAST._IExpr _out349;
            _out349 = DCOMP.COMP.GenPathExpr(_1928_path);
            r = _out349;
            if ((new BigInteger((_1929_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1930_typeExprs;
              _1930_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi38 = new BigInteger((_1929_typeArgs).Count);
              for (BigInteger _1931_i = BigInteger.Zero; _1931_i < _hi38; _1931_i++) {
                RAST._IType _1932_typeExpr;
                RAST._IType _out350;
                _out350 = (this).GenType((_1929_typeArgs).Select(_1931_i), DCOMP.GenTypeContext.@default());
                _1932_typeExpr = _out350;
                _1930_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1930_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1932_typeExpr));
              }
              r = (r).ApplyType(_1930_typeExprs);
            }
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
      if (unmatched95) {
        if (_source95.is_InitializationValue) {
          DAST._IType _1933_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            RAST._IType _1934_typExpr;
            RAST._IType _out353;
            _out353 = (this).GenType(_1933_typ, DCOMP.GenTypeContext.@default());
            _1934_typExpr = _out353;
            if ((_1934_typExpr).IsObjectOrPointer()) {
              r = (_1934_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1934_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
            }
            RAST._IExpr _out354;
            DCOMP._IOwnership _out355;
            (this).FromOwned(r, expectedOwnership, out _out354, out _out355);
            r = _out354;
            resultingOwnership = _out355;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Tuple) {
          Dafny.ISequence<DAST._IExpression> _1935_values = _source95.dtor_Tuple_a0;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1936_exprs;
            _1936_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi39 = new BigInteger((_1935_values).Count);
            for (BigInteger _1937_i = BigInteger.Zero; _1937_i < _hi39; _1937_i++) {
              RAST._IExpr _1938_recursiveGen;
              DCOMP._IOwnership _1939___v159;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1940_recIdents;
              RAST._IExpr _out356;
              DCOMP._IOwnership _out357;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
              (this).GenExpr((_1935_values).Select(_1937_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out356, out _out357, out _out358);
              _1938_recursiveGen = _out356;
              _1939___v159 = _out357;
              _1940_recIdents = _out358;
              _1936_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1936_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1938_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1940_recIdents);
            }
            r = (((new BigInteger((_1935_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1936_exprs)) : (RAST.__default.SystemTuple(_1936_exprs)));
            RAST._IExpr _out359;
            DCOMP._IOwnership _out360;
            (this).FromOwned(r, expectedOwnership, out _out359, out _out360);
            r = _out359;
            resultingOwnership = _out360;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_New) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1941_path = _source95.dtor_path;
          Dafny.ISequence<DAST._IType> _1942_typeArgs = _source95.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1943_args = _source95.dtor_args;
          unmatched95 = false;
          {
            RAST._IExpr _out361;
            _out361 = DCOMP.COMP.GenPathExpr(_1941_path);
            r = _out361;
            if ((new BigInteger((_1942_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1944_typeExprs;
              _1944_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_1942_typeArgs).Count);
              for (BigInteger _1945_i = BigInteger.Zero; _1945_i < _hi40; _1945_i++) {
                RAST._IType _1946_typeExpr;
                RAST._IType _out362;
                _out362 = (this).GenType((_1942_typeArgs).Select(_1945_i), DCOMP.GenTypeContext.@default());
                _1946_typeExpr = _out362;
                _1944_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1944_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1946_typeExpr));
              }
              r = (r).ApplyType(_1944_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1947_arguments;
            _1947_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi41 = new BigInteger((_1943_args).Count);
            for (BigInteger _1948_i = BigInteger.Zero; _1948_i < _hi41; _1948_i++) {
              RAST._IExpr _1949_recursiveGen;
              DCOMP._IOwnership _1950___v160;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1951_recIdents;
              RAST._IExpr _out363;
              DCOMP._IOwnership _out364;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out365;
              (this).GenExpr((_1943_args).Select(_1948_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out363, out _out364, out _out365);
              _1949_recursiveGen = _out363;
              _1950___v160 = _out364;
              _1951_recIdents = _out365;
              _1947_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1947_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1949_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1951_recIdents);
            }
            r = (r).Apply(_1947_arguments);
            RAST._IExpr _out366;
            DCOMP._IOwnership _out367;
            (this).FromOwned(r, expectedOwnership, out _out366, out _out367);
            r = _out366;
            resultingOwnership = _out367;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_NewUninitArray) {
          Dafny.ISequence<DAST._IExpression> _1952_dims = _source95.dtor_dims;
          DAST._IType _1953_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1952_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1954_msg;
              _1954_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1954_msg);
              }
              r = RAST.Expr.create_RawExpr(_1954_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1955_typeGen;
              RAST._IType _out368;
              _out368 = (this).GenType(_1953_typ, DCOMP.GenTypeContext.@default());
              _1955_typeGen = _out368;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1956_dimExprs;
              _1956_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi42 = new BigInteger((_1952_dims).Count);
              for (BigInteger _1957_i = BigInteger.Zero; _1957_i < _hi42; _1957_i++) {
                RAST._IExpr _1958_recursiveGen;
                DCOMP._IOwnership _1959___v161;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1960_recIdents;
                RAST._IExpr _out369;
                DCOMP._IOwnership _out370;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
                (this).GenExpr((_1952_dims).Select(_1957_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out369, out _out370, out _out371);
                _1958_recursiveGen = _out369;
                _1959___v161 = _out370;
                _1960_recIdents = _out371;
                _1956_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1956_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_TypeAscription(_1958_recursiveGen, RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("usize")))));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1960_recIdents);
              }
              if ((new BigInteger((_1952_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1961_class__name;
                _1961_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1952_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1961_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1955_typeGen))).MSel((this).placebos__usize)).Apply(_1956_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1955_typeGen))).Apply(_1956_dimExprs);
              }
            }
            RAST._IExpr _out372;
            DCOMP._IOwnership _out373;
            (this).FromOwned(r, expectedOwnership, out _out372, out _out373);
            r = _out372;
            resultingOwnership = _out373;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_ArrayIndexToInt) {
          DAST._IExpression _1962_underlying = _source95.dtor_value;
          unmatched95 = false;
          {
            RAST._IExpr _1963_recursiveGen;
            DCOMP._IOwnership _1964___v162;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1965_recIdents;
            RAST._IExpr _out374;
            DCOMP._IOwnership _out375;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
            (this).GenExpr(_1962_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out374, out _out375, out _out376);
            _1963_recursiveGen = _out374;
            _1964___v162 = _out375;
            _1965_recIdents = _out376;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1963_recursiveGen);
            readIdents = _1965_recIdents;
            RAST._IExpr _out377;
            DCOMP._IOwnership _out378;
            (this).FromOwned(r, expectedOwnership, out _out377, out _out378);
            r = _out377;
            resultingOwnership = _out378;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_FinalizeNewArray) {
          DAST._IExpression _1966_underlying = _source95.dtor_value;
          DAST._IType _1967_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            RAST._IType _1968_tpe;
            RAST._IType _out379;
            _out379 = (this).GenType(_1967_typ, DCOMP.GenTypeContext.@default());
            _1968_tpe = _out379;
            RAST._IExpr _1969_recursiveGen;
            DCOMP._IOwnership _1970___v163;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1971_recIdents;
            RAST._IExpr _out380;
            DCOMP._IOwnership _out381;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
            (this).GenExpr(_1966_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out380, out _out381, out _out382);
            _1969_recursiveGen = _out380;
            _1970___v163 = _out381;
            _1971_recIdents = _out382;
            readIdents = _1971_recIdents;
            if ((_1968_tpe).IsObjectOrPointer()) {
              RAST._IType _1972_t;
              _1972_t = (_1968_tpe).ObjectOrPointerUnderlying();
              if ((_1972_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1969_recursiveGen);
              } else if ((_1972_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1973_c;
                _1973_c = (_1972_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1973_c)).MSel((this).array__construct)).Apply1(_1969_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1968_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1968_tpe)._ToString(DCOMP.__default.IND)));
              r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            }
            RAST._IExpr _out383;
            DCOMP._IOwnership _out384;
            (this).FromOwned(r, expectedOwnership, out _out383, out _out384);
            r = _out383;
            resultingOwnership = _out384;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_DatatypeValue) {
          DAST._IResolvedType _1974_datatypeType = _source95.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1975_typeArgs = _source95.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1976_variant = _source95.dtor_variant;
          bool _1977_isCo = _source95.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1978_values = _source95.dtor_contents;
          unmatched95 = false;
          {
            RAST._IExpr _out385;
            _out385 = DCOMP.COMP.GenPathExpr((_1974_datatypeType).dtor_path);
            r = _out385;
            Dafny.ISequence<RAST._IType> _1979_genTypeArgs;
            _1979_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi43 = new BigInteger((_1975_typeArgs).Count);
            for (BigInteger _1980_i = BigInteger.Zero; _1980_i < _hi43; _1980_i++) {
              RAST._IType _1981_typeExpr;
              RAST._IType _out386;
              _out386 = (this).GenType((_1975_typeArgs).Select(_1980_i), DCOMP.GenTypeContext.@default());
              _1981_typeExpr = _out386;
              _1979_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1979_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1981_typeExpr));
            }
            if ((new BigInteger((_1975_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1979_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1976_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1982_assignments;
            _1982_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi44 = new BigInteger((_1978_values).Count);
            for (BigInteger _1983_i = BigInteger.Zero; _1983_i < _hi44; _1983_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs66 = (_1978_values).Select(_1983_i);
              Dafny.ISequence<Dafny.Rune> _1984_name = _let_tmp_rhs66.dtor__0;
              DAST._IExpression _1985_value = _let_tmp_rhs66.dtor__1;
              if (_1977_isCo) {
                RAST._IExpr _1986_recursiveGen;
                DCOMP._IOwnership _1987___v164;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1988_recIdents;
                RAST._IExpr _out387;
                DCOMP._IOwnership _out388;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
                (this).GenExpr(_1985_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out387, out _out388, out _out389);
                _1986_recursiveGen = _out387;
                _1987___v164 = _out388;
                _1988_recIdents = _out389;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1988_recIdents);
                Dafny.ISequence<Dafny.Rune> _1989_allReadCloned;
                _1989_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1988_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1990_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1988_recIdents).Elements) {
                    _1990_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1988_recIdents).Contains(_1990_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4326)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1989_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1989_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1990_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1990_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1988_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1988_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1990_next));
                }
                Dafny.ISequence<Dafny.Rune> _1991_wasAssigned;
                _1991_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1989_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1986_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1982_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1982_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1984_name), RAST.Expr.create_RawExpr(_1991_wasAssigned))));
              } else {
                RAST._IExpr _1992_recursiveGen;
                DCOMP._IOwnership _1993___v165;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1994_recIdents;
                RAST._IExpr _out390;
                DCOMP._IOwnership _out391;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out392;
                (this).GenExpr(_1985_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out390, out _out391, out _out392);
                _1992_recursiveGen = _out390;
                _1993___v165 = _out391;
                _1994_recIdents = _out392;
                _1982_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1982_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1984_name), _1992_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1994_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1982_assignments);
            if ((this).IsRcWrapped((_1974_datatypeType).dtor_attributes)) {
              r = RAST.__default.RcNew(r);
            }
            RAST._IExpr _out393;
            DCOMP._IOwnership _out394;
            (this).FromOwned(r, expectedOwnership, out _out393, out _out394);
            r = _out393;
            resultingOwnership = _out394;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Convert) {
          DAST._IExpression _1995___v166 = _source95.dtor_value;
          DAST._IType _1996___v167 = _source95.dtor_from;
          DAST._IType _1997___v168 = _source95.dtor_typ;
          unmatched95 = false;
          {
            RAST._IExpr _out395;
            DCOMP._IOwnership _out396;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out397;
            (this).GenExprConvert(e, selfIdent, env, expectedOwnership, out _out395, out _out396, out _out397);
            r = _out395;
            resultingOwnership = _out396;
            readIdents = _out397;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_SeqConstruct) {
          DAST._IExpression _1998_length = _source95.dtor_length;
          DAST._IExpression _1999_expr = _source95.dtor_elem;
          unmatched95 = false;
          {
            RAST._IExpr _2000_recursiveGen;
            DCOMP._IOwnership _2001___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2002_recIdents;
            RAST._IExpr _out398;
            DCOMP._IOwnership _out399;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
            (this).GenExpr(_1999_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out398, out _out399, out _out400);
            _2000_recursiveGen = _out398;
            _2001___v169 = _out399;
            _2002_recIdents = _out400;
            RAST._IExpr _2003_lengthGen;
            DCOMP._IOwnership _2004___v170;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2005_lengthIdents;
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
            (this).GenExpr(_1998_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out401, out _out402, out _out403);
            _2003_lengthGen = _out401;
            _2004___v170 = _out402;
            _2005_lengthIdents = _out403;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_2000_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_2003_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2002_recIdents, _2005_lengthIdents);
            RAST._IExpr _out404;
            DCOMP._IOwnership _out405;
            (this).FromOwned(r, expectedOwnership, out _out404, out _out405);
            r = _out404;
            resultingOwnership = _out405;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_SeqValue) {
          Dafny.ISequence<DAST._IExpression> _2006_exprs = _source95.dtor_elements;
          DAST._IType _2007_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _2008_genTpe;
            RAST._IType _out406;
            _out406 = (this).GenType(_2007_typ, DCOMP.GenTypeContext.@default());
            _2008_genTpe = _out406;
            BigInteger _2009_i;
            _2009_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2010_args;
            _2010_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2009_i) < (new BigInteger((_2006_exprs).Count))) {
              RAST._IExpr _2011_recursiveGen;
              DCOMP._IOwnership _2012___v171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2013_recIdents;
              RAST._IExpr _out407;
              DCOMP._IOwnership _out408;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
              (this).GenExpr((_2006_exprs).Select(_2009_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out407, out _out408, out _out409);
              _2011_recursiveGen = _out407;
              _2012___v171 = _out408;
              _2013_recIdents = _out409;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2013_recIdents);
              _2010_args = Dafny.Sequence<RAST._IExpr>.Concat(_2010_args, Dafny.Sequence<RAST._IExpr>.FromElements(_2011_recursiveGen));
              _2009_i = (_2009_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_2010_args);
            if ((new BigInteger((_2010_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_2008_genTpe));
            }
            RAST._IExpr _out410;
            DCOMP._IOwnership _out411;
            (this).FromOwned(r, expectedOwnership, out _out410, out _out411);
            r = _out410;
            resultingOwnership = _out411;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_SetValue) {
          Dafny.ISequence<DAST._IExpression> _2014_exprs = _source95.dtor_elements;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2015_generatedValues;
            _2015_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2016_i;
            _2016_i = BigInteger.Zero;
            while ((_2016_i) < (new BigInteger((_2014_exprs).Count))) {
              RAST._IExpr _2017_recursiveGen;
              DCOMP._IOwnership _2018___v172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2019_recIdents;
              RAST._IExpr _out412;
              DCOMP._IOwnership _out413;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
              (this).GenExpr((_2014_exprs).Select(_2016_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out412, out _out413, out _out414);
              _2017_recursiveGen = _out412;
              _2018___v172 = _out413;
              _2019_recIdents = _out414;
              _2015_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2015_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2017_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2019_recIdents);
              _2016_i = (_2016_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_2015_generatedValues);
            RAST._IExpr _out415;
            DCOMP._IOwnership _out416;
            (this).FromOwned(r, expectedOwnership, out _out415, out _out416);
            r = _out415;
            resultingOwnership = _out416;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MultisetValue) {
          Dafny.ISequence<DAST._IExpression> _2020_exprs = _source95.dtor_elements;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2021_generatedValues;
            _2021_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2022_i;
            _2022_i = BigInteger.Zero;
            while ((_2022_i) < (new BigInteger((_2020_exprs).Count))) {
              RAST._IExpr _2023_recursiveGen;
              DCOMP._IOwnership _2024___v173;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2025_recIdents;
              RAST._IExpr _out417;
              DCOMP._IOwnership _out418;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
              (this).GenExpr((_2020_exprs).Select(_2022_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out417, out _out418, out _out419);
              _2023_recursiveGen = _out417;
              _2024___v173 = _out418;
              _2025_recIdents = _out419;
              _2021_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2021_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2023_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2025_recIdents);
              _2022_i = (_2022_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_2021_generatedValues);
            RAST._IExpr _out420;
            DCOMP._IOwnership _out421;
            (this).FromOwned(r, expectedOwnership, out _out420, out _out421);
            r = _out420;
            resultingOwnership = _out421;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_ToMultiset) {
          DAST._IExpression _2026_expr = _source95.dtor_ToMultiset_a0;
          unmatched95 = false;
          {
            RAST._IExpr _2027_recursiveGen;
            DCOMP._IOwnership _2028___v174;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2029_recIdents;
            RAST._IExpr _out422;
            DCOMP._IOwnership _out423;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
            (this).GenExpr(_2026_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out422, out _out423, out _out424);
            _2027_recursiveGen = _out422;
            _2028___v174 = _out423;
            _2029_recIdents = _out424;
            r = ((_2027_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2029_recIdents;
            RAST._IExpr _out425;
            DCOMP._IOwnership _out426;
            (this).FromOwned(r, expectedOwnership, out _out425, out _out426);
            r = _out425;
            resultingOwnership = _out426;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapValue) {
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2030_mapElems = _source95.dtor_mapElems;
          unmatched95 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _2031_generatedValues;
            _2031_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2032_i;
            _2032_i = BigInteger.Zero;
            while ((_2032_i) < (new BigInteger((_2030_mapElems).Count))) {
              RAST._IExpr _2033_recursiveGenKey;
              DCOMP._IOwnership _2034___v175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2035_recIdentsKey;
              RAST._IExpr _out427;
              DCOMP._IOwnership _out428;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out429;
              (this).GenExpr(((_2030_mapElems).Select(_2032_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out427, out _out428, out _out429);
              _2033_recursiveGenKey = _out427;
              _2034___v175 = _out428;
              _2035_recIdentsKey = _out429;
              RAST._IExpr _2036_recursiveGenValue;
              DCOMP._IOwnership _2037___v176;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2038_recIdentsValue;
              RAST._IExpr _out430;
              DCOMP._IOwnership _out431;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out432;
              (this).GenExpr(((_2030_mapElems).Select(_2032_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out430, out _out431, out _out432);
              _2036_recursiveGenValue = _out430;
              _2037___v176 = _out431;
              _2038_recIdentsValue = _out432;
              _2031_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_2031_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_2033_recursiveGenKey, _2036_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2035_recIdentsKey), _2038_recIdentsValue);
              _2032_i = (_2032_i) + (BigInteger.One);
            }
            _2032_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2039_arguments;
            _2039_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2032_i) < (new BigInteger((_2031_generatedValues).Count))) {
              RAST._IExpr _2040_genKey;
              _2040_genKey = ((_2031_generatedValues).Select(_2032_i)).dtor__0;
              RAST._IExpr _2041_genValue;
              _2041_genValue = ((_2031_generatedValues).Select(_2032_i)).dtor__1;
              _2039_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2039_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _2040_genKey, _2041_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _2032_i = (_2032_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_2039_arguments);
            RAST._IExpr _out433;
            DCOMP._IOwnership _out434;
            (this).FromOwned(r, expectedOwnership, out _out433, out _out434);
            r = _out433;
            resultingOwnership = _out434;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_SeqUpdate) {
          DAST._IExpression _2042_expr = _source95.dtor_expr;
          DAST._IExpression _2043_index = _source95.dtor_indexExpr;
          DAST._IExpression _2044_value = _source95.dtor_value;
          unmatched95 = false;
          {
            RAST._IExpr _2045_exprR;
            DCOMP._IOwnership _2046___v177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2047_exprIdents;
            RAST._IExpr _out435;
            DCOMP._IOwnership _out436;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out437;
            (this).GenExpr(_2042_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out435, out _out436, out _out437);
            _2045_exprR = _out435;
            _2046___v177 = _out436;
            _2047_exprIdents = _out437;
            RAST._IExpr _2048_indexR;
            DCOMP._IOwnership _2049_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2050_indexIdents;
            RAST._IExpr _out438;
            DCOMP._IOwnership _out439;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
            (this).GenExpr(_2043_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out438, out _out439, out _out440);
            _2048_indexR = _out438;
            _2049_indexOwnership = _out439;
            _2050_indexIdents = _out440;
            RAST._IExpr _2051_valueR;
            DCOMP._IOwnership _2052_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2053_valueIdents;
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
            (this).GenExpr(_2044_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out441, out _out442, out _out443);
            _2051_valueR = _out441;
            _2052_valueOwnership = _out442;
            _2053_valueIdents = _out443;
            r = ((_2045_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2048_indexR, _2051_valueR));
            RAST._IExpr _out444;
            DCOMP._IOwnership _out445;
            (this).FromOwned(r, expectedOwnership, out _out444, out _out445);
            r = _out444;
            resultingOwnership = _out445;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2047_exprIdents, _2050_indexIdents), _2053_valueIdents);
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapUpdate) {
          DAST._IExpression _2054_expr = _source95.dtor_expr;
          DAST._IExpression _2055_index = _source95.dtor_indexExpr;
          DAST._IExpression _2056_value = _source95.dtor_value;
          unmatched95 = false;
          {
            RAST._IExpr _2057_exprR;
            DCOMP._IOwnership _2058___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2059_exprIdents;
            RAST._IExpr _out446;
            DCOMP._IOwnership _out447;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
            (this).GenExpr(_2054_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out446, out _out447, out _out448);
            _2057_exprR = _out446;
            _2058___v178 = _out447;
            _2059_exprIdents = _out448;
            RAST._IExpr _2060_indexR;
            DCOMP._IOwnership _2061_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2062_indexIdents;
            RAST._IExpr _out449;
            DCOMP._IOwnership _out450;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
            (this).GenExpr(_2055_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out449, out _out450, out _out451);
            _2060_indexR = _out449;
            _2061_indexOwnership = _out450;
            _2062_indexIdents = _out451;
            RAST._IExpr _2063_valueR;
            DCOMP._IOwnership _2064_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2065_valueIdents;
            RAST._IExpr _out452;
            DCOMP._IOwnership _out453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
            (this).GenExpr(_2056_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out452, out _out453, out _out454);
            _2063_valueR = _out452;
            _2064_valueOwnership = _out453;
            _2065_valueIdents = _out454;
            r = ((_2057_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2060_indexR, _2063_valueR));
            RAST._IExpr _out455;
            DCOMP._IOwnership _out456;
            (this).FromOwned(r, expectedOwnership, out _out455, out _out456);
            r = _out455;
            resultingOwnership = _out456;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2059_exprIdents, _2062_indexIdents), _2065_valueIdents);
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_This) {
          unmatched95 = false;
          {
            DCOMP._ISelfInfo _source96 = selfIdent;
            bool unmatched96 = true;
            if (unmatched96) {
              if (_source96.is_ThisTyped) {
                Dafny.ISequence<Dafny.Rune> _2066_id = _source96.dtor_rSelfName;
                DAST._IType _2067_dafnyType = _source96.dtor_dafnyType;
                unmatched96 = false;
                {
                  RAST._IExpr _out457;
                  DCOMP._IOwnership _out458;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out459;
                  (this).GenIdent(_2066_id, selfIdent, env, expectedOwnership, out _out457, out _out458, out _out459);
                  r = _out457;
                  resultingOwnership = _out458;
                  readIdents = _out459;
                }
              }
            }
            if (unmatched96) {
              DCOMP._ISelfInfo _2068_None = _source96;
              unmatched96 = false;
              {
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"this outside of a method\")"));
                RAST._IExpr _out460;
                DCOMP._IOwnership _out461;
                (this).FromOwned(r, expectedOwnership, out _out460, out _out461);
                r = _out460;
                resultingOwnership = _out461;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              }
            }
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Ite) {
          DAST._IExpression _2069_cond = _source95.dtor_cond;
          DAST._IExpression _2070_t = _source95.dtor_thn;
          DAST._IExpression _2071_f = _source95.dtor_els;
          unmatched95 = false;
          {
            RAST._IExpr _2072_cond;
            DCOMP._IOwnership _2073___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2074_recIdentsCond;
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
            (this).GenExpr(_2069_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out462, out _out463, out _out464);
            _2072_cond = _out462;
            _2073___v179 = _out463;
            _2074_recIdentsCond = _out464;
            RAST._IExpr _2075_fExpr;
            DCOMP._IOwnership _2076_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2077_recIdentsF;
            RAST._IExpr _out465;
            DCOMP._IOwnership _out466;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out467;
            (this).GenExpr(_2071_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out465, out _out466, out _out467);
            _2075_fExpr = _out465;
            _2076_fOwned = _out466;
            _2077_recIdentsF = _out467;
            RAST._IExpr _2078_tExpr;
            DCOMP._IOwnership _2079___v180;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2080_recIdentsT;
            RAST._IExpr _out468;
            DCOMP._IOwnership _out469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out470;
            (this).GenExpr(_2070_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out468, out _out469, out _out470);
            _2078_tExpr = _out468;
            _2079___v180 = _out469;
            _2080_recIdentsT = _out470;
            r = RAST.Expr.create_IfExpr(_2072_cond, _2078_tExpr, _2075_fExpr);
            RAST._IExpr _out471;
            DCOMP._IOwnership _out472;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out471, out _out472);
            r = _out471;
            resultingOwnership = _out472;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2074_recIdentsCond, _2080_recIdentsT), _2077_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source95.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _2081_e = _source95.dtor_expr;
            DAST.Format._IUnaryOpFormat _2082_format = _source95.dtor_format1;
            unmatched95 = false;
            {
              RAST._IExpr _2083_recursiveGen;
              DCOMP._IOwnership _2084___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2085_recIdents;
              RAST._IExpr _out473;
              DCOMP._IOwnership _out474;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out475;
              (this).GenExpr(_2081_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out473, out _out474, out _out475);
              _2083_recursiveGen = _out473;
              _2084___v181 = _out474;
              _2085_recIdents = _out475;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _2083_recursiveGen, _2082_format);
              RAST._IExpr _out476;
              DCOMP._IOwnership _out477;
              (this).FromOwned(r, expectedOwnership, out _out476, out _out477);
              r = _out476;
              resultingOwnership = _out477;
              readIdents = _2085_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source95.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _2086_e = _source95.dtor_expr;
            DAST.Format._IUnaryOpFormat _2087_format = _source95.dtor_format1;
            unmatched95 = false;
            {
              RAST._IExpr _2088_recursiveGen;
              DCOMP._IOwnership _2089___v182;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2090_recIdents;
              RAST._IExpr _out478;
              DCOMP._IOwnership _out479;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
              (this).GenExpr(_2086_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out478, out _out479, out _out480);
              _2088_recursiveGen = _out478;
              _2089___v182 = _out479;
              _2090_recIdents = _out480;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _2088_recursiveGen, _2087_format);
              RAST._IExpr _out481;
              DCOMP._IOwnership _out482;
              (this).FromOwned(r, expectedOwnership, out _out481, out _out482);
              r = _out481;
              resultingOwnership = _out482;
              readIdents = _2090_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source95.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _2091_e = _source95.dtor_expr;
            DAST.Format._IUnaryOpFormat _2092_format = _source95.dtor_format1;
            unmatched95 = false;
            {
              RAST._IExpr _2093_recursiveGen;
              DCOMP._IOwnership _2094_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2095_recIdents;
              RAST._IExpr _out483;
              DCOMP._IOwnership _out484;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out485;
              (this).GenExpr(_2091_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out483, out _out484, out _out485);
              _2093_recursiveGen = _out483;
              _2094_recOwned = _out484;
              _2095_recIdents = _out485;
              r = ((_2093_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out486;
              DCOMP._IOwnership _out487;
              (this).FromOwned(r, expectedOwnership, out _out486, out _out487);
              r = _out486;
              resultingOwnership = _out487;
              readIdents = _2095_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_BinOp) {
          DAST._IBinOp _2096___v183 = _source95.dtor_op;
          DAST._IExpression _2097___v184 = _source95.dtor_left;
          DAST._IExpression _2098___v185 = _source95.dtor_right;
          DAST.Format._IBinaryOpFormat _2099___v186 = _source95.dtor_format2;
          unmatched95 = false;
          RAST._IExpr _out488;
          DCOMP._IOwnership _out489;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out490;
          (this).GenExprBinary(e, selfIdent, env, expectedOwnership, out _out488, out _out489, out _out490);
          r = _out488;
          resultingOwnership = _out489;
          readIdents = _out490;
        }
      }
      if (unmatched95) {
        if (_source95.is_ArrayLen) {
          DAST._IExpression _2100_expr = _source95.dtor_expr;
          DAST._IType _2101_exprType = _source95.dtor_exprType;
          BigInteger _2102_dim = _source95.dtor_dim;
          bool _2103_native = _source95.dtor_native;
          unmatched95 = false;
          {
            RAST._IExpr _2104_recursiveGen;
            DCOMP._IOwnership _2105___v187;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2106_recIdents;
            RAST._IExpr _out491;
            DCOMP._IOwnership _out492;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
            (this).GenExpr(_2100_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out491, out _out492, out _out493);
            _2104_recursiveGen = _out491;
            _2105___v187 = _out492;
            _2106_recIdents = _out493;
            RAST._IType _2107_arrayType;
            RAST._IType _out494;
            _out494 = (this).GenType(_2101_exprType, DCOMP.GenTypeContext.@default());
            _2107_arrayType = _out494;
            if (!((_2107_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2108_msg;
              _2108_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2107_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2108_msg);
              r = RAST.Expr.create_RawExpr(_2108_msg);
            } else {
              RAST._IType _2109_underlying;
              _2109_underlying = (_2107_arrayType).ObjectOrPointerUnderlying();
              if (((_2102_dim).Sign == 0) && ((_2109_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2104_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2102_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2104_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = (((this).read__macro).Apply1(_2104_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Length"), Std.Strings.__default.OfNat(_2102_dim)));
                }
              }
              if (!(_2103_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out495;
            DCOMP._IOwnership _out496;
            (this).FromOwned(r, expectedOwnership, out _out495, out _out496);
            r = _out495;
            resultingOwnership = _out496;
            readIdents = _2106_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapKeys) {
          DAST._IExpression _2110_expr = _source95.dtor_expr;
          unmatched95 = false;
          {
            RAST._IExpr _2111_recursiveGen;
            DCOMP._IOwnership _2112___v188;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2113_recIdents;
            RAST._IExpr _out497;
            DCOMP._IOwnership _out498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
            (this).GenExpr(_2110_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out497, out _out498, out _out499);
            _2111_recursiveGen = _out497;
            _2112___v188 = _out498;
            _2113_recIdents = _out499;
            readIdents = _2113_recIdents;
            r = ((_2111_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out500;
            DCOMP._IOwnership _out501;
            (this).FromOwned(r, expectedOwnership, out _out500, out _out501);
            r = _out500;
            resultingOwnership = _out501;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapValues) {
          DAST._IExpression _2114_expr = _source95.dtor_expr;
          unmatched95 = false;
          {
            RAST._IExpr _2115_recursiveGen;
            DCOMP._IOwnership _2116___v189;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2117_recIdents;
            RAST._IExpr _out502;
            DCOMP._IOwnership _out503;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
            (this).GenExpr(_2114_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out502, out _out503, out _out504);
            _2115_recursiveGen = _out502;
            _2116___v189 = _out503;
            _2117_recIdents = _out504;
            readIdents = _2117_recIdents;
            r = ((_2115_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out505;
            DCOMP._IOwnership _out506;
            (this).FromOwned(r, expectedOwnership, out _out505, out _out506);
            r = _out505;
            resultingOwnership = _out506;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_SelectFn) {
          DAST._IExpression _2118_on = _source95.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2119_field = _source95.dtor_field;
          bool _2120_isDatatype = _source95.dtor_onDatatype;
          bool _2121_isStatic = _source95.dtor_isStatic;
          BigInteger _2122_arity = _source95.dtor_arity;
          unmatched95 = false;
          {
            RAST._IExpr _2123_onExpr;
            DCOMP._IOwnership _2124_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2125_recIdents;
            RAST._IExpr _out507;
            DCOMP._IOwnership _out508;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out509;
            (this).GenExpr(_2118_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out507, out _out508, out _out509);
            _2123_onExpr = _out507;
            _2124_onOwned = _out508;
            _2125_recIdents = _out509;
            Dafny.ISequence<Dafny.Rune> _2126_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2127_onString;
            _2127_onString = (_2123_onExpr)._ToString(DCOMP.__default.IND);
            if (_2121_isStatic) {
              _2126_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2127_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_2119_field));
            } else {
              _2126_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2126_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2126_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2127_onString), ((object.Equals(_2124_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2128_args;
              _2128_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2129_i;
              _2129_i = BigInteger.Zero;
              while ((_2129_i) < (_2122_arity)) {
                if ((_2129_i).Sign == 1) {
                  _2128_args = Dafny.Sequence<Dafny.Rune>.Concat(_2128_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2128_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2128_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2129_i));
                _2129_i = (_2129_i) + (BigInteger.One);
              }
              _2126_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2126_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2128_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2126_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2126_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_2119_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2128_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2126_s = Dafny.Sequence<Dafny.Rune>.Concat(_2126_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2126_s = Dafny.Sequence<Dafny.Rune>.Concat(_2126_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2130_typeShape;
            _2130_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2131_i;
            _2131_i = BigInteger.Zero;
            while ((_2131_i) < (_2122_arity)) {
              if ((_2131_i).Sign == 1) {
                _2130_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2130_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2130_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2130_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2131_i = (_2131_i) + (BigInteger.One);
            }
            _2130_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2130_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2126_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2126_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2130_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2126_s);
            RAST._IExpr _out510;
            DCOMP._IOwnership _out511;
            (this).FromOwned(r, expectedOwnership, out _out510, out _out511);
            r = _out510;
            resultingOwnership = _out511;
            readIdents = _2125_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Select) {
          DAST._IExpression expr0 = _source95.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2132_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<DAST._IType> _2133_typeArgs = expr0.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _2134_field = _source95.dtor_field;
            bool _2135_isConstant = _source95.dtor_isConstant;
            bool _2136_isDatatype = _source95.dtor_onDatatype;
            DAST._IType _2137_fieldType = _source95.dtor_fieldType;
            unmatched95 = false;
            {
              RAST._IExpr _2138_onExpr;
              DCOMP._IOwnership _2139_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2140_recIdents;
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExpr(DAST.Expression.create_Companion(_2132_c, _2133_typeArgs), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out512, out _out513, out _out514);
              _2138_onExpr = _out512;
              _2139_onOwned = _out513;
              _2140_recIdents = _out514;
              r = ((_2138_onExpr).MSel(DCOMP.__default.escapeName(_2134_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              (this).FromOwned(r, expectedOwnership, out _out515, out _out516);
              r = _out515;
              resultingOwnership = _out516;
              readIdents = _2140_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Select) {
          DAST._IExpression _2141_on = _source95.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2142_field = _source95.dtor_field;
          bool _2143_isConstant = _source95.dtor_isConstant;
          bool _2144_isDatatype = _source95.dtor_onDatatype;
          DAST._IType _2145_fieldType = _source95.dtor_fieldType;
          unmatched95 = false;
          {
            if (_2144_isDatatype) {
              RAST._IExpr _2146_onExpr;
              DCOMP._IOwnership _2147_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2148_recIdents;
              RAST._IExpr _out517;
              DCOMP._IOwnership _out518;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
              (this).GenExpr(_2141_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out517, out _out518, out _out519);
              _2146_onExpr = _out517;
              _2147_onOwned = _out518;
              _2148_recIdents = _out519;
              r = ((_2146_onExpr).Sel(DCOMP.__default.escapeName(_2142_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2149_typ;
              RAST._IType _out520;
              _out520 = (this).GenType(_2145_fieldType, DCOMP.GenTypeContext.@default());
              _2149_typ = _out520;
              RAST._IExpr _out521;
              DCOMP._IOwnership _out522;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out521, out _out522);
              r = _out521;
              resultingOwnership = _out522;
              readIdents = _2148_recIdents;
            } else {
              RAST._IExpr _2150_onExpr;
              DCOMP._IOwnership _2151_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2152_recIdents;
              RAST._IExpr _out523;
              DCOMP._IOwnership _out524;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
              (this).GenExpr(_2141_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out523, out _out524, out _out525);
              _2150_onExpr = _out523;
              _2151_onOwned = _out524;
              _2152_recIdents = _out525;
              r = _2150_onExpr;
              if (!object.Equals(_2150_onExpr, RAST.__default.self)) {
                RAST._IExpr _source97 = _2150_onExpr;
                bool unmatched97 = true;
                if (unmatched97) {
                  if (_source97.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source97.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source97.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name15 = underlying5.dtor_name;
                        if (object.Equals(name15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          DAST.Format._IUnaryOpFormat _2153___v190 = _source97.dtor_format;
                          unmatched97 = false;
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                        }
                      }
                    }
                  }
                }
                if (unmatched97) {
                  RAST._IExpr _2154___v191 = _source97;
                  unmatched97 = false;
                }
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeName(_2142_field));
              if (_2143_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out526;
              DCOMP._IOwnership _out527;
              (this).FromOwned(r, expectedOwnership, out _out526, out _out527);
              r = _out526;
              resultingOwnership = _out527;
              readIdents = _2152_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Index) {
          DAST._IExpression _2155_on = _source95.dtor_expr;
          DAST._ICollKind _2156_collKind = _source95.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2157_indices = _source95.dtor_indices;
          unmatched95 = false;
          {
            RAST._IExpr _2158_onExpr;
            DCOMP._IOwnership _2159_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2160_recIdents;
            RAST._IExpr _out528;
            DCOMP._IOwnership _out529;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
            (this).GenExpr(_2155_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out528, out _out529, out _out530);
            _2158_onExpr = _out528;
            _2159_onOwned = _out529;
            _2160_recIdents = _out530;
            readIdents = _2160_recIdents;
            r = _2158_onExpr;
            BigInteger _2161_i;
            _2161_i = BigInteger.Zero;
            while ((_2161_i) < (new BigInteger((_2157_indices).Count))) {
              if (object.Equals(_2156_collKind, DAST.CollKind.create_Array())) {
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              RAST._IExpr _2162_idx;
              DCOMP._IOwnership _2163_idxOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2164_recIdentsIdx;
              RAST._IExpr _out531;
              DCOMP._IOwnership _out532;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
              (this).GenExpr((_2157_indices).Select(_2161_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out531, out _out532, out _out533);
              _2162_idx = _out531;
              _2163_idxOwned = _out532;
              _2164_recIdentsIdx = _out533;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2162_idx);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2164_recIdentsIdx);
              _2161_i = (_2161_i) + (BigInteger.One);
            }
            RAST._IExpr _out534;
            DCOMP._IOwnership _out535;
            (this).FromOwned(r, expectedOwnership, out _out534, out _out535);
            r = _out534;
            resultingOwnership = _out535;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_IndexRange) {
          DAST._IExpression _2165_on = _source95.dtor_expr;
          bool _2166_isArray = _source95.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2167_low = _source95.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2168_high = _source95.dtor_high;
          unmatched95 = false;
          {
            RAST._IExpr _2169_onExpr;
            DCOMP._IOwnership _2170_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2171_recIdents;
            RAST._IExpr _out536;
            DCOMP._IOwnership _out537;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
            (this).GenExpr(_2165_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out536, out _out537, out _out538);
            _2169_onExpr = _out536;
            _2170_onOwned = _out537;
            _2171_recIdents = _out538;
            readIdents = _2171_recIdents;
            Dafny.ISequence<Dafny.Rune> _2172_methodName;
            _2172_methodName = (((_2167_low).is_Some) ? ((((_2168_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2168_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2173_arguments;
            _2173_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source98 = _2167_low;
            bool unmatched98 = true;
            if (unmatched98) {
              if (_source98.is_Some) {
                DAST._IExpression _2174_l = _source98.dtor_value;
                unmatched98 = false;
                {
                  RAST._IExpr _2175_lExpr;
                  DCOMP._IOwnership _2176___v192;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2177_recIdentsL;
                  RAST._IExpr _out539;
                  DCOMP._IOwnership _out540;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
                  (this).GenExpr(_2174_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out539, out _out540, out _out541);
                  _2175_lExpr = _out539;
                  _2176___v192 = _out540;
                  _2177_recIdentsL = _out541;
                  _2173_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2173_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2175_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2177_recIdentsL);
                }
              }
            }
            if (unmatched98) {
              unmatched98 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source99 = _2168_high;
            bool unmatched99 = true;
            if (unmatched99) {
              if (_source99.is_Some) {
                DAST._IExpression _2178_h = _source99.dtor_value;
                unmatched99 = false;
                {
                  RAST._IExpr _2179_hExpr;
                  DCOMP._IOwnership _2180___v193;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2181_recIdentsH;
                  RAST._IExpr _out542;
                  DCOMP._IOwnership _out543;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
                  (this).GenExpr(_2178_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out542, out _out543, out _out544);
                  _2179_hExpr = _out542;
                  _2180___v193 = _out543;
                  _2181_recIdentsH = _out544;
                  _2173_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2173_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2179_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2181_recIdentsH);
                }
              }
            }
            if (unmatched99) {
              unmatched99 = false;
            }
            r = _2169_onExpr;
            if (_2166_isArray) {
              if (!(_2172_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2172_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2172_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2172_methodName))).Apply(_2173_arguments);
            } else {
              if (!(_2172_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2172_methodName)).Apply(_2173_arguments);
              }
            }
            RAST._IExpr _out545;
            DCOMP._IOwnership _out546;
            (this).FromOwned(r, expectedOwnership, out _out545, out _out546);
            r = _out545;
            resultingOwnership = _out546;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_TupleSelect) {
          DAST._IExpression _2182_on = _source95.dtor_expr;
          BigInteger _2183_idx = _source95.dtor_index;
          DAST._IType _2184_fieldType = _source95.dtor_fieldType;
          unmatched95 = false;
          {
            RAST._IExpr _2185_onExpr;
            DCOMP._IOwnership _2186_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2187_recIdents;
            RAST._IExpr _out547;
            DCOMP._IOwnership _out548;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
            (this).GenExpr(_2182_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out547, out _out548, out _out549);
            _2185_onExpr = _out547;
            _2186_onOwnership = _out548;
            _2187_recIdents = _out549;
            Dafny.ISequence<Dafny.Rune> _2188_selName;
            _2188_selName = Std.Strings.__default.OfNat(_2183_idx);
            DAST._IType _source100 = _2184_fieldType;
            bool unmatched100 = true;
            if (unmatched100) {
              if (_source100.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2189_tps = _source100.dtor_Tuple_a0;
                unmatched100 = false;
                if (((_2184_fieldType).is_Tuple) && ((new BigInteger((_2189_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2188_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2188_selName);
                }
              }
            }
            if (unmatched100) {
              DAST._IType _2190___v194 = _source100;
              unmatched100 = false;
            }
            r = ((_2185_onExpr).Sel(_2188_selName)).Clone();
            RAST._IExpr _out550;
            DCOMP._IOwnership _out551;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out550, out _out551);
            r = _out550;
            resultingOwnership = _out551;
            readIdents = _2187_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Call) {
          DAST._IExpression _2191_on = _source95.dtor_on;
          DAST._ICallName _2192_name = _source95.dtor_callName;
          Dafny.ISequence<DAST._IType> _2193_typeArgs = _source95.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2194_args = _source95.dtor_args;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2195_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2196_recIdents;
            Dafny.ISequence<RAST._IType> _2197_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2198_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out552;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
            Dafny.ISequence<RAST._IType> _out554;
            Std.Wrappers._IOption<DAST._IResolvedType> _out555;
            (this).GenArgs(selfIdent, _2192_name, _2193_typeArgs, _2194_args, env, out _out552, out _out553, out _out554, out _out555);
            _2195_argExprs = _out552;
            _2196_recIdents = _out553;
            _2197_typeExprs = _out554;
            _2198_fullNameQualifier = _out555;
            readIdents = _2196_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source101 = _2198_fullNameQualifier;
            bool unmatched101 = true;
            if (unmatched101) {
              if (_source101.is_Some) {
                DAST._IResolvedType value11 = _source101.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2199_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2200_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2201_base = value11.dtor_kind;
                Dafny.ISequence<DAST._IAttribute> _2202___v195 = value11.dtor_attributes;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2203___v196 = value11.dtor_properMethods;
                Dafny.ISequence<DAST._IType> _2204___v197 = value11.dtor_extendedTypes;
                unmatched101 = false;
                RAST._IExpr _2205_fullPath;
                RAST._IExpr _out556;
                _out556 = DCOMP.COMP.GenPathExpr(_2199_path);
                _2205_fullPath = _out556;
                Dafny.ISequence<RAST._IType> _2206_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out557;
                _out557 = (this).GenTypeArgs(_2200_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2206_onTypeExprs = _out557;
                RAST._IExpr _2207_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2208_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2209_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2201_base).is_Trait) || ((_2201_base).is_Class)) {
                  RAST._IExpr _out558;
                  DCOMP._IOwnership _out559;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
                  (this).GenExpr(_2191_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out558, out _out559, out _out560);
                  _2207_onExpr = _out558;
                  _2208_recOwnership = _out559;
                  _2209_recIdents = _out560;
                  _2207_onExpr = ((this).read__macro).Apply1(_2207_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2209_recIdents);
                } else {
                  RAST._IExpr _out561;
                  DCOMP._IOwnership _out562;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
                  (this).GenExpr(_2191_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out561, out _out562, out _out563);
                  _2207_onExpr = _out561;
                  _2208_recOwnership = _out562;
                  _2209_recIdents = _out563;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2209_recIdents);
                }
                r = ((((_2205_fullPath).ApplyType(_2206_onTypeExprs)).MSel(DCOMP.__default.escapeName((_2192_name).dtor_name))).ApplyType(_2197_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2207_onExpr), _2195_argExprs));
                RAST._IExpr _out564;
                DCOMP._IOwnership _out565;
                (this).FromOwned(r, expectedOwnership, out _out564, out _out565);
                r = _out564;
                resultingOwnership = _out565;
              }
            }
            if (unmatched101) {
              Std.Wrappers._IOption<DAST._IResolvedType> _2210___v198 = _source101;
              unmatched101 = false;
              RAST._IExpr _2211_onExpr;
              DCOMP._IOwnership _2212___v199;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2213_recIdents;
              RAST._IExpr _out566;
              DCOMP._IOwnership _out567;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
              (this).GenExpr(_2191_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out566, out _out567, out _out568);
              _2211_onExpr = _out566;
              _2212___v199 = _out567;
              _2213_recIdents = _out568;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2213_recIdents);
              Dafny.ISequence<Dafny.Rune> _2214_renderedName;
              _2214_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
                DAST._ICallName _source102 = _2192_name;
                bool unmatched102 = true;
                if (unmatched102) {
                  if (_source102.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _2215_ident = _source102.dtor_name;
                    Std.Wrappers._IOption<DAST._IType> _2216___v200 = _source102.dtor_onType;
                    Std.Wrappers._IOption<DAST._IFormal> _2217___v201 = _source102.dtor_receiverArgs;
                    Dafny.ISequence<DAST._IFormal> _2218___v202 = _source102.dtor_signature;
                    unmatched102 = false;
                    return DCOMP.__default.escapeName(_2215_ident);
                  }
                }
                if (unmatched102) {
                  bool disjunctiveMatch15 = false;
                  if (_source102.is_MapBuilderAdd) {
                    disjunctiveMatch15 = true;
                  }
                  if (_source102.is_SetBuilderAdd) {
                    disjunctiveMatch15 = true;
                  }
                  if (disjunctiveMatch15) {
                    unmatched102 = false;
                    return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("add");
                  }
                }
                if (unmatched102) {
                  bool disjunctiveMatch16 = false;
                  disjunctiveMatch16 = true;
                  disjunctiveMatch16 = true;
                  if (disjunctiveMatch16) {
                    unmatched102 = false;
                    return Dafny.Sequence<Dafny.Rune>.UnicodeFromString("build");
                  }
                }
                throw new System.Exception("unexpected control point");
              }))();
              DAST._IExpression _source103 = _2191_on;
              bool unmatched103 = true;
              if (unmatched103) {
                if (_source103.is_Companion) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2219___v203 = _source103.dtor_Companion_a0;
                  Dafny.ISequence<DAST._IType> _2220___v204 = _source103.dtor_typeArgs;
                  unmatched103 = false;
                  {
                    _2211_onExpr = (_2211_onExpr).MSel(_2214_renderedName);
                  }
                }
              }
              if (unmatched103) {
                DAST._IExpression _2221___v205 = _source103;
                unmatched103 = false;
                {
                  if (!object.Equals(_2211_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source104 = _2192_name;
                    bool unmatched104 = true;
                    if (unmatched104) {
                      if (_source104.is_CallName) {
                        Dafny.ISequence<Dafny.Rune> _2222___v206 = _source104.dtor_name;
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source104.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2223_tpe = onType2.dtor_value;
                          Std.Wrappers._IOption<DAST._IFormal> _2224___v207 = _source104.dtor_receiverArgs;
                          Dafny.ISequence<DAST._IFormal> _2225___v208 = _source104.dtor_signature;
                          unmatched104 = false;
                          RAST._IType _2226_typ;
                          RAST._IType _out569;
                          _out569 = (this).GenType(_2223_tpe, DCOMP.GenTypeContext.@default());
                          _2226_typ = _out569;
                          if ((_2226_typ).IsObjectOrPointer()) {
                            _2211_onExpr = ((this).read__macro).Apply1(_2211_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched104) {
                      DAST._ICallName _2227___v209 = _source104;
                      unmatched104 = false;
                    }
                  }
                  _2211_onExpr = (_2211_onExpr).Sel(_2214_renderedName);
                }
              }
              r = ((_2211_onExpr).ApplyType(_2197_typeExprs)).Apply(_2195_argExprs);
              RAST._IExpr _out570;
              DCOMP._IOwnership _out571;
              (this).FromOwned(r, expectedOwnership, out _out570, out _out571);
              r = _out570;
              resultingOwnership = _out571;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Lambda) {
          Dafny.ISequence<DAST._IFormal> _2228_paramsDafny = _source95.dtor_params;
          DAST._IType _2229_retType = _source95.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2230_body = _source95.dtor_body;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2231_params;
            Dafny.ISequence<RAST._IFormal> _out572;
            _out572 = (this).GenParams(_2228_paramsDafny);
            _2231_params = _out572;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2232_paramNames;
            _2232_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2233_paramTypesMap;
            _2233_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi45 = new BigInteger((_2231_params).Count);
            for (BigInteger _2234_i = BigInteger.Zero; _2234_i < _hi45; _2234_i++) {
              Dafny.ISequence<Dafny.Rune> _2235_name;
              _2235_name = ((_2231_params).Select(_2234_i)).dtor_name;
              _2232_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2232_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2235_name));
              _2233_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2233_paramTypesMap, _2235_name, ((_2231_params).Select(_2234_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2236_subEnv;
            _2236_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2232_paramNames, _2233_paramTypesMap));
            RAST._IExpr _2237_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2238_recIdents;
            DCOMP._IEnvironment _2239___v210;
            RAST._IExpr _out573;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out574;
            DCOMP._IEnvironment _out575;
            (this).GenStmts(_2230_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2236_subEnv, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out573, out _out574, out _out575);
            _2237_recursiveGen = _out573;
            _2238_recIdents = _out574;
            _2239___v210 = _out575;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2238_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2238_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2240_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll7 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_7 in (_2240_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2241_name = (Dafny.ISequence<Dafny.Rune>)_compr_7;
                if ((_2240_paramNames).Contains(_2241_name)) {
                  _coll7.Add(_2241_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll7);
            }))())(_2232_paramNames));
            RAST._IExpr _2242_allReadCloned;
            _2242_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2238_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2243_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2238_recIdents).Elements) {
                _2243_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_2238_recIdents).Contains(_2243_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 4788)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2243_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2244_selfCloned;
                DCOMP._IOwnership _2245___v211;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2246___v212;
                RAST._IExpr _out576;
                DCOMP._IOwnership _out577;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out578;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out576, out _out577, out _out578);
                _2244_selfCloned = _out576;
                _2245___v211 = _out577;
                _2246___v212 = _out578;
                _2242_allReadCloned = (_2242_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2244_selfCloned)));
              } else if (!((_2232_paramNames).Contains(_2243_next))) {
                RAST._IExpr _2247_copy;
                _2247_copy = (RAST.Expr.create_Identifier(_2243_next)).Clone();
                _2242_allReadCloned = (_2242_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2243_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2247_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2243_next));
              }
              _2238_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2238_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2243_next));
            }
            RAST._IType _2248_retTypeGen;
            RAST._IType _out579;
            _out579 = (this).GenType(_2229_retType, DCOMP.GenTypeContext.InFn());
            _2248_retTypeGen = _out579;
            r = RAST.Expr.create_Block((_2242_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2231_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2248_retTypeGen), RAST.Expr.create_Block(_2237_recursiveGen)))));
            RAST._IExpr _out580;
            DCOMP._IOwnership _out581;
            (this).FromOwned(r, expectedOwnership, out _out580, out _out581);
            r = _out580;
            resultingOwnership = _out581;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_BetaRedex) {
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2249_values = _source95.dtor_values;
          DAST._IType _2250_retType = _source95.dtor_retType;
          DAST._IExpression _2251_expr = _source95.dtor_expr;
          unmatched95 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2252_paramNames;
            _2252_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2253_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out582;
            _out582 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2254_value) => {
              return (_2254_value).dtor__0;
            })), _2249_values));
            _2253_paramFormals = _out582;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2255_paramTypes;
            _2255_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2256_paramNamesSet;
            _2256_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi46 = new BigInteger((_2249_values).Count);
            for (BigInteger _2257_i = BigInteger.Zero; _2257_i < _hi46; _2257_i++) {
              Dafny.ISequence<Dafny.Rune> _2258_name;
              _2258_name = (((_2249_values).Select(_2257_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2259_rName;
              _2259_rName = DCOMP.__default.escapeName(_2258_name);
              _2252_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2252_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2259_rName));
              _2255_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2255_paramTypes, _2259_rName, ((_2253_paramFormals).Select(_2257_i)).dtor_tpe);
              _2256_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2256_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2259_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi47 = new BigInteger((_2249_values).Count);
            for (BigInteger _2260_i = BigInteger.Zero; _2260_i < _hi47; _2260_i++) {
              RAST._IType _2261_typeGen;
              RAST._IType _out583;
              _out583 = (this).GenType((((_2249_values).Select(_2260_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2261_typeGen = _out583;
              RAST._IExpr _2262_valueGen;
              DCOMP._IOwnership _2263___v213;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2264_recIdents;
              RAST._IExpr _out584;
              DCOMP._IOwnership _out585;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
              (this).GenExpr(((_2249_values).Select(_2260_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out584, out _out585, out _out586);
              _2262_valueGen = _out584;
              _2263___v213 = _out585;
              _2264_recIdents = _out586;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_2249_values).Select(_2260_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2261_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2262_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2264_recIdents);
            }
            DCOMP._IEnvironment _2265_newEnv;
            _2265_newEnv = DCOMP.Environment.create(_2252_paramNames, _2255_paramTypes);
            RAST._IExpr _2266_recGen;
            DCOMP._IOwnership _2267_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2268_recIdents;
            RAST._IExpr _out587;
            DCOMP._IOwnership _out588;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
            (this).GenExpr(_2251_expr, selfIdent, _2265_newEnv, expectedOwnership, out _out587, out _out588, out _out589);
            _2266_recGen = _out587;
            _2267_recOwned = _out588;
            _2268_recIdents = _out589;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2268_recIdents, _2256_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2266_recGen));
            RAST._IExpr _out590;
            DCOMP._IOwnership _out591;
            (this).FromOwnership(r, _2267_recOwned, expectedOwnership, out _out590, out _out591);
            r = _out590;
            resultingOwnership = _out591;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2269_name = _source95.dtor_name;
          DAST._IType _2270_tpe = _source95.dtor_typ;
          DAST._IExpression _2271_value = _source95.dtor_value;
          DAST._IExpression _2272_iifeBody = _source95.dtor_iifeBody;
          unmatched95 = false;
          {
            RAST._IExpr _2273_valueGen;
            DCOMP._IOwnership _2274___v214;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2275_recIdents;
            RAST._IExpr _out592;
            DCOMP._IOwnership _out593;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
            (this).GenExpr(_2271_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out592, out _out593, out _out594);
            _2273_valueGen = _out592;
            _2274___v214 = _out593;
            _2275_recIdents = _out594;
            readIdents = _2275_recIdents;
            RAST._IType _2276_valueTypeGen;
            RAST._IType _out595;
            _out595 = (this).GenType(_2270_tpe, DCOMP.GenTypeContext.InFn());
            _2276_valueTypeGen = _out595;
            RAST._IExpr _2277_bodyGen;
            DCOMP._IOwnership _2278___v215;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2279_bodyIdents;
            RAST._IExpr _out596;
            DCOMP._IOwnership _out597;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
            (this).GenExpr(_2272_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out596, out _out597, out _out598);
            _2277_bodyGen = _out596;
            _2278___v215 = _out597;
            _2279_bodyIdents = _out598;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2279_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_2269_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_2269_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_2276_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2273_valueGen))).Then(_2277_bodyGen));
            RAST._IExpr _out599;
            DCOMP._IOwnership _out600;
            (this).FromOwned(r, expectedOwnership, out _out599, out _out600);
            r = _out599;
            resultingOwnership = _out600;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Apply) {
          DAST._IExpression _2280_func = _source95.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2281_args = _source95.dtor_args;
          unmatched95 = false;
          {
            RAST._IExpr _2282_funcExpr;
            DCOMP._IOwnership _2283___v216;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2284_recIdents;
            RAST._IExpr _out601;
            DCOMP._IOwnership _out602;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out603;
            (this).GenExpr(_2280_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out601, out _out602, out _out603);
            _2282_funcExpr = _out601;
            _2283___v216 = _out602;
            _2284_recIdents = _out603;
            readIdents = _2284_recIdents;
            Dafny.ISequence<RAST._IExpr> _2285_rArgs;
            _2285_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi48 = new BigInteger((_2281_args).Count);
            for (BigInteger _2286_i = BigInteger.Zero; _2286_i < _hi48; _2286_i++) {
              RAST._IExpr _2287_argExpr;
              DCOMP._IOwnership _2288_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2289_argIdents;
              RAST._IExpr _out604;
              DCOMP._IOwnership _out605;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
              (this).GenExpr((_2281_args).Select(_2286_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out604, out _out605, out _out606);
              _2287_argExpr = _out604;
              _2288_argOwned = _out605;
              _2289_argIdents = _out606;
              _2285_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2285_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2287_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2289_argIdents);
            }
            r = (_2282_funcExpr).Apply(_2285_rArgs);
            RAST._IExpr _out607;
            DCOMP._IOwnership _out608;
            (this).FromOwned(r, expectedOwnership, out _out607, out _out608);
            r = _out607;
            resultingOwnership = _out608;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_TypeTest) {
          DAST._IExpression _2290_on = _source95.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2291_dType = _source95.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2292_variant = _source95.dtor_variant;
          unmatched95 = false;
          {
            RAST._IExpr _2293_exprGen;
            DCOMP._IOwnership _2294___v217;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2295_recIdents;
            RAST._IExpr _out609;
            DCOMP._IOwnership _out610;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out611;
            (this).GenExpr(_2290_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out609, out _out610, out _out611);
            _2293_exprGen = _out609;
            _2294___v217 = _out610;
            _2295_recIdents = _out611;
            RAST._IType _2296_dTypePath;
            RAST._IType _out612;
            _out612 = DCOMP.COMP.GenPath(_2291_dType);
            _2296_dTypePath = _out612;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2293_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2296_dTypePath).MSel(DCOMP.__default.escapeName(_2292_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out613;
            DCOMP._IOwnership _out614;
            (this).FromOwned(r, expectedOwnership, out _out613, out _out614);
            r = _out613;
            resultingOwnership = _out614;
            readIdents = _2295_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_BoolBoundedPool) {
          unmatched95 = false;
          {
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("[false, true]"));
            RAST._IExpr _out615;
            DCOMP._IOwnership _out616;
            (this).FromOwned(r, expectedOwnership, out _out615, out _out616);
            r = _out615;
            resultingOwnership = _out616;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_SetBoundedPool) {
          DAST._IExpression _2297_of = _source95.dtor_of;
          unmatched95 = false;
          {
            RAST._IExpr _2298_exprGen;
            DCOMP._IOwnership _2299___v218;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2300_recIdents;
            RAST._IExpr _out617;
            DCOMP._IOwnership _out618;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out619;
            (this).GenExpr(_2297_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out617, out _out618, out _out619);
            _2298_exprGen = _out617;
            _2299___v218 = _out618;
            _2300_recIdents = _out619;
            r = ((_2298_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out620;
            DCOMP._IOwnership _out621;
            (this).FromOwned(r, expectedOwnership, out _out620, out _out621);
            r = _out620;
            resultingOwnership = _out621;
            readIdents = _2300_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_SeqBoundedPool) {
          DAST._IExpression _2301_of = _source95.dtor_of;
          bool _2302_includeDuplicates = _source95.dtor_includeDuplicates;
          unmatched95 = false;
          {
            RAST._IExpr _2303_exprGen;
            DCOMP._IOwnership _2304___v219;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2305_recIdents;
            RAST._IExpr _out622;
            DCOMP._IOwnership _out623;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out624;
            (this).GenExpr(_2301_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out622, out _out623, out _out624);
            _2303_exprGen = _out622;
            _2304___v219 = _out623;
            _2305_recIdents = _out624;
            r = ((_2303_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2302_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out625;
            DCOMP._IOwnership _out626;
            (this).FromOwned(r, expectedOwnership, out _out625, out _out626);
            r = _out625;
            resultingOwnership = _out626;
            readIdents = _2305_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapBoundedPool) {
          DAST._IExpression _2306_of = _source95.dtor_of;
          unmatched95 = false;
          {
            RAST._IExpr _2307_exprGen;
            DCOMP._IOwnership _2308___v220;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2309_recIdents;
            RAST._IExpr _out627;
            DCOMP._IOwnership _out628;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out629;
            (this).GenExpr(_2306_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out627, out _out628, out _out629);
            _2307_exprGen = _out627;
            _2308___v220 = _out628;
            _2309_recIdents = _out629;
            r = ((((_2307_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2309_recIdents;
            RAST._IExpr _out630;
            DCOMP._IOwnership _out631;
            (this).FromOwned(r, expectedOwnership, out _out630, out _out631);
            r = _out630;
            resultingOwnership = _out631;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_IntRange) {
          DAST._IExpression _2310_lo = _source95.dtor_lo;
          DAST._IExpression _2311_hi = _source95.dtor_hi;
          bool _2312_up = _source95.dtor_up;
          unmatched95 = false;
          {
            RAST._IExpr _2313_lo;
            DCOMP._IOwnership _2314___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2315_recIdentsLo;
            RAST._IExpr _out632;
            DCOMP._IOwnership _out633;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
            (this).GenExpr(_2310_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out632, out _out633, out _out634);
            _2313_lo = _out632;
            _2314___v221 = _out633;
            _2315_recIdentsLo = _out634;
            RAST._IExpr _2316_hi;
            DCOMP._IOwnership _2317___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2318_recIdentsHi;
            RAST._IExpr _out635;
            DCOMP._IOwnership _out636;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out637;
            (this).GenExpr(_2311_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out635, out _out636, out _out637);
            _2316_hi = _out635;
            _2317___v222 = _out636;
            _2318_recIdentsHi = _out637;
            if (_2312_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2313_lo, _2316_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2316_hi, _2313_lo));
            }
            RAST._IExpr _out638;
            DCOMP._IOwnership _out639;
            (this).FromOwned(r, expectedOwnership, out _out638, out _out639);
            r = _out638;
            resultingOwnership = _out639;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2315_recIdentsLo, _2318_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnboundedIntRange) {
          DAST._IExpression _2319_start = _source95.dtor_start;
          bool _2320_up = _source95.dtor_up;
          unmatched95 = false;
          {
            RAST._IExpr _2321_start;
            DCOMP._IOwnership _2322___v223;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2323_recIdentStart;
            RAST._IExpr _out640;
            DCOMP._IOwnership _out641;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out642;
            (this).GenExpr(_2319_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out640, out _out641, out _out642);
            _2321_start = _out640;
            _2322___v223 = _out641;
            _2323_recIdentStart = _out642;
            if (_2320_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2321_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2321_start);
            }
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            (this).FromOwned(r, expectedOwnership, out _out643, out _out644);
            r = _out643;
            resultingOwnership = _out644;
            readIdents = _2323_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapBuilder) {
          DAST._IType _2324_keyType = _source95.dtor_keyType;
          DAST._IType _2325_valueType = _source95.dtor_valueType;
          unmatched95 = false;
          {
            RAST._IType _2326_kType;
            RAST._IType _out645;
            _out645 = (this).GenType(_2324_keyType, DCOMP.GenTypeContext.@default());
            _2326_kType = _out645;
            RAST._IType _2327_vType;
            RAST._IType _out646;
            _out646 = (this).GenType(_2325_valueType, DCOMP.GenTypeContext.@default());
            _2327_vType = _out646;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2326_kType, _2327_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out647;
            DCOMP._IOwnership _out648;
            (this).FromOwned(r, expectedOwnership, out _out647, out _out648);
            r = _out647;
            resultingOwnership = _out648;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_SetBuilder) {
          DAST._IType _2328_elemType = _source95.dtor_elemType;
          unmatched95 = false;
          {
            RAST._IType _2329_eType;
            RAST._IType _out649;
            _out649 = (this).GenType(_2328_elemType, DCOMP.GenTypeContext.@default());
            _2329_eType = _out649;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2329_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out650;
            DCOMP._IOwnership _out651;
            (this).FromOwned(r, expectedOwnership, out _out650, out _out651);
            r = _out650;
            resultingOwnership = _out651;
            return ;
          }
        }
      }
      if (unmatched95) {
        DAST._IType _2330_elemType = _source95.dtor_elemType;
        DAST._IExpression _2331_collection = _source95.dtor_collection;
        bool _2332_is__forall = _source95.dtor_is__forall;
        DAST._IExpression _2333_lambda = _source95.dtor_lambda;
        unmatched95 = false;
        {
          RAST._IType _2334_tpe;
          RAST._IType _out652;
          _out652 = (this).GenType(_2330_elemType, DCOMP.GenTypeContext.@default());
          _2334_tpe = _out652;
          RAST._IExpr _2335_collectionGen;
          DCOMP._IOwnership _2336___v224;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2337_recIdents;
          RAST._IExpr _out653;
          DCOMP._IOwnership _out654;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
          (this).GenExpr(_2331_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out653, out _out654, out _out655);
          _2335_collectionGen = _out653;
          _2336___v224 = _out654;
          _2337_recIdents = _out655;
          Dafny.ISequence<DAST._IAttribute> _2338_extraAttributes;
          _2338_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2331_collection).is_IntRange) || ((_2331_collection).is_UnboundedIntRange)) || ((_2331_collection).is_SeqBoundedPool)) {
            _2338_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2333_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2339_formals;
            _2339_formals = (_2333_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2340_newFormals;
            _2340_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi49 = new BigInteger((_2339_formals).Count);
            for (BigInteger _2341_i = BigInteger.Zero; _2341_i < _hi49; _2341_i++) {
              var _pat_let_tv141 = _2338_extraAttributes;
              var _pat_let_tv142 = _2339_formals;
              _2340_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2340_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2339_formals).Select(_2341_i), _pat_let38_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let38_0, _2342_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv141, ((_pat_let_tv142).Select(_2341_i)).dtor_attributes), _pat_let39_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let39_0, _2343_dt__update_hattributes_h0 => DAST.Formal.create((_2342_dt__update__tmp_h0).dtor_name, (_2342_dt__update__tmp_h0).dtor_typ, _2343_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv143 = _2340_newFormals;
            DAST._IExpression _2344_newLambda;
            _2344_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2333_lambda, _pat_let40_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let40_0, _2345_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv143, _pat_let41_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let41_0, _2346_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2346_dt__update_hparams_h0, (_2345_dt__update__tmp_h1).dtor_retType, (_2345_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2347_lambdaGen;
            DCOMP._IOwnership _2348___v225;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2349_recLambdaIdents;
            RAST._IExpr _out656;
            DCOMP._IOwnership _out657;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out658;
            (this).GenExpr(_2344_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out656, out _out657, out _out658);
            _2347_lambdaGen = _out656;
            _2348___v225 = _out657;
            _2349_recLambdaIdents = _out658;
            Dafny.ISequence<Dafny.Rune> _2350_fn;
            _2350_fn = ((_2332_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2335_collectionGen).Sel(_2350_fn)).Apply1(((_2347_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2337_recIdents, _2349_recLambdaIdents);
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Quantifier without an inline lambda"));
            r = RAST.Expr.create_RawExpr((this.error).dtor_value);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
          }
          RAST._IExpr _out659;
          DCOMP._IOwnership _out660;
          (this).FromOwned(r, expectedOwnership, out _out659, out _out660);
          r = _out659;
          resultingOwnership = _out660;
        }
      }
    }
    public Dafny.ISequence<Dafny.Rune> Compile(Dafny.ISequence<DAST._IModule> p)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(warnings, unconditional_panic)]\n");
      s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#![allow(nonstandard_style)]\n"));
      BigInteger _2351_i;
      _2351_i = BigInteger.Zero;
      while ((_2351_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2352_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _2353_m;
        RAST._IMod _out661;
        _out661 = (this).GenModule((p).Select(_2351_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2353_m = _out661;
        _2352_generated = (_2353_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_2351_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2352_generated);
        _2351_i = (_2351_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2354_i;
      _2354_i = BigInteger.Zero;
      while ((_2354_i) < (new BigInteger((fullName).Count))) {
        if ((_2354_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2354_i)));
        _2354_i = (_2354_i) + (BigInteger.One);
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
  }
} // end of namespace DCOMP