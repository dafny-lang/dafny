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
      BigInteger _hi12 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1303_i = BigInteger.Zero; _1303_i < _hi12; _1303_i++) {
        DAST._IDatatypeCtor _1304_ctor;
        _1304_ctor = ((c).dtor_ctors).Select(_1303_i);
        Dafny.ISequence<RAST._IField> _1305_ctorArgs;
        _1305_ctorArgs = Dafny.Sequence<RAST._IField>.FromElements();
        bool _1306_isNumeric;
        _1306_isNumeric = false;
        BigInteger _hi13 = new BigInteger(((_1304_ctor).dtor_args).Count);
        for (BigInteger _1307_j = BigInteger.Zero; _1307_j < _hi13; _1307_j++) {
          DAST._IDatatypeDtor _1308_dtor;
          _1308_dtor = ((_1304_ctor).dtor_args).Select(_1307_j);
          RAST._IType _1309_formalType;
          RAST._IType _out74;
          _out74 = (this).GenType(((_1308_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
          _1309_formalType = _out74;
          Dafny.ISequence<Dafny.Rune> _1310_formalName;
          _1310_formalName = DCOMP.__default.escapeName(((_1308_dtor).dtor_formal).dtor_name);
          if (((_1307_j).Sign == 0) && ((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")).Equals(_1310_formalName))) {
            _1306_isNumeric = true;
          }
          if ((((_1307_j).Sign != 0) && (_1306_isNumeric)) && (!(Std.Strings.__default.OfNat(_1307_j)).Equals(_1310_formalName))) {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formal extern names were supposed to be numeric but got "), _1310_formalName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" instead of ")), Std.Strings.__default.OfNat(_1307_j)));
            _1306_isNumeric = false;
          }
          if ((c).dtor_isCo) {
            _1305_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1305_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1310_formalName, RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("LazyFieldWrapper")), Dafny.Sequence<RAST._IType>.FromElements(_1309_formalType))))));
          } else {
            _1305_ctorArgs = Dafny.Sequence<RAST._IField>.Concat(_1305_ctorArgs, Dafny.Sequence<RAST._IField>.FromElements(RAST.Field.create(RAST.Visibility.create_PRIV(), RAST.Formal.create(_1310_formalName, _1309_formalType))));
          }
        }
        RAST._IFields _1311_namedFields;
        _1311_namedFields = RAST.Fields.create_NamedFields(_1305_ctorArgs);
        if (_1306_isNumeric) {
          _1311_namedFields = (_1311_namedFields).ToNamelessFields();
        }
        _1302_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1302_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(DCOMP.__default.escapeName((_1304_ctor).dtor_name), _1311_namedFields)));
      }
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1312_selfPath;
      _1312_selfPath = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements((c).dtor_name);
      Dafny.ISequence<RAST._IImplMember> _1313_implBodyRaw;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _1314_traitBodies;
      Dafny.ISequence<RAST._IImplMember> _out75;
      Dafny.IMap<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>,Dafny.ISequence<RAST._IImplMember>> _out76;
      (this).GenClassImplBody((c).dtor_body, false, DAST.Type.create_UserDefined(DAST.ResolvedType.create(_1312_selfPath, _1297_typeParamsSeq, DAST.ResolvedTypeBase.create_Datatype(), (c).dtor_attributes, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(), Dafny.Sequence<DAST._IType>.FromElements())), _1297_typeParamsSeq, out _out75, out _out76);
      _1313_implBodyRaw = _out75;
      _1314_traitBodies = _out76;
      Dafny.ISequence<RAST._IImplMember> _1315_implBody;
      _1315_implBody = _1313_implBodyRaw;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1316_emittedFields;
      _1316_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _hi14 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1317_i = BigInteger.Zero; _1317_i < _hi14; _1317_i++) {
        DAST._IDatatypeCtor _1318_ctor;
        _1318_ctor = ((c).dtor_ctors).Select(_1317_i);
        BigInteger _hi15 = new BigInteger(((_1318_ctor).dtor_args).Count);
        for (BigInteger _1319_j = BigInteger.Zero; _1319_j < _hi15; _1319_j++) {
          DAST._IDatatypeDtor _1320_dtor;
          _1320_dtor = ((_1318_ctor).dtor_args).Select(_1319_j);
          Dafny.ISequence<Dafny.Rune> _1321_callName;
          _1321_callName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1320_dtor).dtor_callName, DCOMP.__default.escapeName(((_1320_dtor).dtor_formal).dtor_name));
          if (!((_1316_emittedFields).Contains(_1321_callName))) {
            _1316_emittedFields = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1316_emittedFields, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1321_callName));
            RAST._IType _1322_formalType;
            RAST._IType _out77;
            _out77 = (this).GenType(((_1320_dtor).dtor_formal).dtor_typ, DCOMP.GenTypeContext.@default());
            _1322_formalType = _out77;
            Dafny.ISequence<RAST._IMatchCase> _1323_cases;
            _1323_cases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
            BigInteger _hi16 = new BigInteger(((c).dtor_ctors).Count);
            for (BigInteger _1324_k = BigInteger.Zero; _1324_k < _hi16; _1324_k++) {
              DAST._IDatatypeCtor _1325_ctor2;
              _1325_ctor2 = ((c).dtor_ctors).Select(_1324_k);
              Dafny.ISequence<Dafny.Rune> _1326_pattern;
              _1326_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1301_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName((_1325_ctor2).dtor_name));
              Dafny.ISequence<Dafny.Rune> _1327_rhs = Dafny.Sequence<Dafny.Rune>.Empty;
              Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1328_hasMatchingField;
              _1328_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
              Dafny.ISequence<Dafny.Rune> _1329_patternInner;
              _1329_patternInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              bool _1330_isNumeric;
              _1330_isNumeric = false;
              BigInteger _hi17 = new BigInteger(((_1325_ctor2).dtor_args).Count);
              for (BigInteger _1331_l = BigInteger.Zero; _1331_l < _hi17; _1331_l++) {
                DAST._IDatatypeDtor _1332_dtor2;
                _1332_dtor2 = ((_1325_ctor2).dtor_args).Select(_1331_l);
                Dafny.ISequence<Dafny.Rune> _1333_patternName;
                _1333_patternName = DCOMP.__default.escapeDtor(((_1332_dtor2).dtor_formal).dtor_name);
                if (((_1331_l).Sign == 0) && ((_1333_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
                  _1330_isNumeric = true;
                }
                if (_1330_isNumeric) {
                  _1333_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1332_dtor2).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1331_l)));
                }
                if (object.Equals(((_1320_dtor).dtor_formal).dtor_name, ((_1332_dtor2).dtor_formal).dtor_name)) {
                  _1328_hasMatchingField = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1333_patternName);
                }
                _1329_patternInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1329_patternInner, _1333_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              if (_1330_isNumeric) {
                _1326_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1326_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1329_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
              } else {
                _1326_pattern = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1326_pattern, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1329_patternInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
              }
              if ((_1328_hasMatchingField).is_Some) {
                if ((c).dtor_isCo) {
                  _1327_rhs = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::ops::Deref::deref(&"), (_1328_hasMatchingField).dtor_value), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0)"));
                } else {
                  _1327_rhs = Dafny.Sequence<Dafny.Rune>.Concat((_1328_hasMatchingField).dtor_value, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
                }
              } else {
                _1327_rhs = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!(\"field does not exist on this variant\")");
              }
              RAST._IMatchCase _1334_ctorMatch;
              _1334_ctorMatch = RAST.MatchCase.create(_1326_pattern, RAST.Expr.create_RawExpr(_1327_rhs));
              _1323_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1323_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(_1334_ctorMatch));
            }
            if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
              _1323_cases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1323_cases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1301_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("panic!()")))));
            }
            RAST._IExpr _1335_methodBody;
            _1335_methodBody = RAST.Expr.create_Match(RAST.__default.self, _1323_cases);
            _1315_implBody = Dafny.Sequence<RAST._IImplMember>.Concat(_1315_implBody, Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(_1321_callName, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Borrowed(_1322_formalType)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1335_methodBody)))));
          }
        }
      }
      Dafny.ISequence<RAST._IType> _1336_coerceTypes;
      _1336_coerceTypes = Dafny.Sequence<RAST._IType>.FromElements();
      Dafny.ISequence<RAST._ITypeParamDecl> _1337_rCoerceTypeParams;
      _1337_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      Dafny.ISequence<RAST._IFormal> _1338_coerceArguments;
      _1338_coerceArguments = Dafny.Sequence<RAST._IFormal>.FromElements();
      Dafny.IMap<DAST._IType,DAST._IType> _1339_coerceMap;
      _1339_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.FromElements();
      Dafny.IMap<RAST._IType,RAST._IType> _1340_rCoerceMap;
      _1340_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.FromElements();
      Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr> _1341_coerceMapToArg;
      _1341_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements();
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IType> _1342_types;
        _1342_types = Dafny.Sequence<RAST._IType>.FromElements();
        BigInteger _hi18 = new BigInteger(((c).dtor_typeParams).Count);
        for (BigInteger _1343_typeI = BigInteger.Zero; _1343_typeI < _hi18; _1343_typeI++) {
          DAST._ITypeArgDecl _1344_typeParam;
          _1344_typeParam = ((c).dtor_typeParams).Select(_1343_typeI);
          DAST._IType _1345_typeArg;
          RAST._ITypeParamDecl _1346_rTypeParamDecl;
          DAST._IType _out78;
          RAST._ITypeParamDecl _out79;
          (this).GenTypeParam(_1344_typeParam, out _out78, out _out79);
          _1345_typeArg = _out78;
          _1346_rTypeParamDecl = _out79;
          RAST._IType _1347_rTypeArg;
          RAST._IType _out80;
          _out80 = (this).GenType(_1345_typeArg, DCOMP.GenTypeContext.@default());
          _1347_rTypeArg = _out80;
          _1342_types = Dafny.Sequence<RAST._IType>.Concat(_1342_types, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("marker"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("PhantomData")), Dafny.Sequence<RAST._IType>.FromElements(_1347_rTypeArg))));
          DAST._ITypeArgDecl _1348_coerceTypeParam;
          _1348_coerceTypeParam = Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_1344_typeParam, _pat_let9_0 => Dafny.Helpers.Let<DAST._ITypeArgDecl, DAST._ITypeArgDecl>(_pat_let9_0, _1349_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_T"), Std.Strings.__default.OfNat(_1343_typeI)), _pat_let10_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, DAST._ITypeArgDecl>(_pat_let10_0, _1350_dt__update_hname_h0 => DAST.TypeArgDecl.create(_1350_dt__update_hname_h0, (_1349_dt__update__tmp_h0).dtor_bounds)))));
          DAST._IType _1351_coerceTypeArg;
          RAST._ITypeParamDecl _1352_rCoerceTypeParamDecl;
          DAST._IType _out81;
          RAST._ITypeParamDecl _out82;
          (this).GenTypeParam(_1348_coerceTypeParam, out _out81, out _out82);
          _1351_coerceTypeArg = _out81;
          _1352_rCoerceTypeParamDecl = _out82;
          _1339_coerceMap = Dafny.Map<DAST._IType, DAST._IType>.Merge(_1339_coerceMap, Dafny.Map<DAST._IType, DAST._IType>.FromElements(new Dafny.Pair<DAST._IType, DAST._IType>(_1345_typeArg, _1351_coerceTypeArg)));
          RAST._IType _1353_rCoerceType;
          RAST._IType _out83;
          _out83 = (this).GenType(_1351_coerceTypeArg, DCOMP.GenTypeContext.@default());
          _1353_rCoerceType = _out83;
          _1340_rCoerceMap = Dafny.Map<RAST._IType, RAST._IType>.Merge(_1340_rCoerceMap, Dafny.Map<RAST._IType, RAST._IType>.FromElements(new Dafny.Pair<RAST._IType, RAST._IType>(_1347_rTypeArg, _1353_rCoerceType)));
          _1336_coerceTypes = Dafny.Sequence<RAST._IType>.Concat(_1336_coerceTypes, Dafny.Sequence<RAST._IType>.FromElements(_1353_rCoerceType));
          _1337_rCoerceTypeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1337_rCoerceTypeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1352_rCoerceTypeParamDecl));
          Dafny.ISequence<Dafny.Rune> _1354_coerceFormal;
          _1354_coerceFormal = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f_"), Std.Strings.__default.OfNat(_1343_typeI));
          _1341_coerceMapToArg = Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Merge(_1341_coerceMapToArg, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements(new Dafny.Pair<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>(_System.Tuple2<RAST._IType, RAST._IType>.create(_1347_rTypeArg, _1353_rCoerceType), (RAST.Expr.create_Identifier(_1354_coerceFormal)).Clone())));
          _1338_coerceArguments = Dafny.Sequence<RAST._IFormal>.Concat(_1338_coerceArguments, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1354_coerceFormal, RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(_1347_rTypeArg), _1353_rCoerceType))))));
        }
        _1302_ctors = Dafny.Sequence<RAST._IEnumCase>.Concat(_1302_ctors, Dafny.Sequence<RAST._IEnumCase>.FromElements(RAST.EnumCase.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_PhantomVariant"), RAST.Fields.create_NamelessFields(Std.Collections.Seq.__default.Map<RAST._IType, RAST._INamelessField>(((System.Func<RAST._IType, RAST._INamelessField>)((_1355_tpe) => {
  return RAST.NamelessField.create(RAST.Visibility.create_PRIV(), _1355_tpe);
})), _1342_types)))));
      }
      bool _1356_cIsEq;
      _1356_cIsEq = (this).DatatypeIsEq(c);
      s = Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_EnumDecl(RAST.Enum.create(((_1356_cIsEq) ? (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(PartialEq, Clone)]"))) : (Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("#[derive(Clone)]")))), _1301_datatypeName, _1299_rTypeParamsDecls, _1302_ctors)), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1299_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams), _1300_whereConstraints, _1315_implBody)));
      Dafny.ISequence<RAST._IMatchCase> _1357_printImplBodyCases;
      _1357_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1358_hashImplBodyCases;
      _1358_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      Dafny.ISequence<RAST._IMatchCase> _1359_coerceImplBodyCases;
      _1359_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.FromElements();
      BigInteger _hi19 = new BigInteger(((c).dtor_ctors).Count);
      for (BigInteger _1360_i = BigInteger.Zero; _1360_i < _hi19; _1360_i++) {
        DAST._IDatatypeCtor _1361_ctor;
        _1361_ctor = ((c).dtor_ctors).Select(_1360_i);
        Dafny.ISequence<Dafny.Rune> _1362_ctorMatch;
        _1362_ctorMatch = DCOMP.__default.escapeName((_1361_ctor).dtor_name);
        Dafny.ISequence<Dafny.Rune> _1363_modulePrefix;
        _1363_modulePrefix = ((((((c).dtor_enclosingModule))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_module"))) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")) : (Dafny.Sequence<Dafny.Rune>.Concat((((c).dtor_enclosingModule)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("."))));
        Dafny.ISequence<Dafny.Rune> _1364_ctorName;
        _1364_ctorName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1363_modulePrefix, ((c).dtor_name)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".")), ((_1361_ctor).dtor_name));
        if (((new BigInteger((_1364_ctorName).Count)) >= (new BigInteger(13))) && (((_1364_ctorName).Subsequence(BigInteger.Zero, new BigInteger(13))).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System.Tuple")))) {
          _1364_ctorName = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        }
        RAST._IExpr _1365_printRhs;
        _1365_printRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \""), _1364_ctorName), (((_1361_ctor).dtor_hasAnyArgs) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(\")?")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\")?")))));
        RAST._IExpr _1366_hashRhs;
        _1366_hashRhs = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        Dafny.ISequence<RAST._IAssignIdentifier> _1367_coerceRhsArgs;
        _1367_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        bool _1368_isNumeric;
        _1368_isNumeric = false;
        Dafny.ISequence<Dafny.Rune> _1369_ctorMatchInner;
        _1369_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
        BigInteger _hi20 = new BigInteger(((_1361_ctor).dtor_args).Count);
        for (BigInteger _1370_j = BigInteger.Zero; _1370_j < _hi20; _1370_j++) {
          DAST._IDatatypeDtor _1371_dtor;
          _1371_dtor = ((_1361_ctor).dtor_args).Select(_1370_j);
          Dafny.ISequence<Dafny.Rune> _1372_patternName;
          _1372_patternName = DCOMP.__default.escapeField(((_1371_dtor).dtor_formal).dtor_name);
          DAST._IType _1373_formalType;
          _1373_formalType = ((_1371_dtor).dtor_formal).dtor_typ;
          if (((_1370_j).Sign == 0) && ((_1372_patternName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")))) {
            _1368_isNumeric = true;
          }
          if (_1368_isNumeric) {
            _1372_patternName = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.GetOr((_1371_dtor).dtor_callName, Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("v"), Std.Strings.__default.OfNat(_1370_j)));
          }
          _1366_hashRhs = (_1366_hashRhs).Then(((RAST.Expr.create_Identifier(_1372_patternName)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).Apply1(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"))));
          _1369_ctorMatchInner = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1369_ctorMatchInner, _1372_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
          if ((_1370_j).Sign == 1) {
            _1365_printRhs = (_1365_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \", \")?")));
          }
          _1365_printRhs = (_1365_printRhs).Then(RAST.Expr.create_RawExpr((((_1373_formalType).is_Arrow) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \"<function>\")?")) : (Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyPrint::fmt_print("), _1372_patternName), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", _formatter, false)?"))))));
          RAST._IExpr _1374_coerceRhsArg = RAST.Expr.Default();
          RAST._IType _1375_formalTpe;
          RAST._IType _out84;
          _out84 = (this).GenType(_1373_formalType, DCOMP.GenTypeContext.@default());
          _1375_formalTpe = _out84;
          DAST._IType _1376_newFormalType;
          _1376_newFormalType = (_1373_formalType).Replace(_1339_coerceMap);
          RAST._IType _1377_newFormalTpe;
          _1377_newFormalTpe = (_1375_formalTpe).Replace(_1340_rCoerceMap);
          Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1378_upcastConverter;
          _1378_upcastConverter = (this).UpcastConversionLambda(_1373_formalType, _1375_formalTpe, _1376_newFormalType, _1377_newFormalTpe, _1341_coerceMapToArg);
          if ((_1378_upcastConverter).is_Success) {
            RAST._IExpr _1379_coercionFunction;
            _1379_coercionFunction = (_1378_upcastConverter).dtor_value;
            _1374_coerceRhsArg = (_1379_coercionFunction).Apply1(RAST.Expr.create_Identifier(_1372_patternName));
          } else {
            (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Could not generate coercion function for contructor "), Std.Strings.__default.OfNat(_1370_j)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" of ")), _1301_datatypeName));
            _1374_coerceRhsArg = RAST.Expr.create_Identifier((this.error).dtor_value);
          }
          _1367_coerceRhsArgs = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1367_coerceRhsArgs, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(_1372_patternName, _1374_coerceRhsArg)));
        }
        RAST._IExpr _1380_coerceRhs;
        _1380_coerceRhs = RAST.Expr.create_StructBuild((RAST.Expr.create_Identifier(_1301_datatypeName)).MSel(DCOMP.__default.escapeName((_1361_ctor).dtor_name)), _1367_coerceRhsArgs);
        if (_1368_isNumeric) {
          _1362_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1362_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _1369_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"));
        } else {
          _1362_ctorMatch = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1362_ctorMatch, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{")), _1369_ctorMatchInner), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
        }
        if ((_1361_ctor).dtor_hasAnyArgs) {
          _1365_printRhs = (_1365_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("write!(_formatter, \")\")?")));
        }
        _1365_printRhs = (_1365_printRhs).Then(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ok(())")));
        _1357_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1357_printImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1301_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1362_ctorMatch), RAST.Expr.create_Block(_1365_printRhs))));
        _1358_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1358_hashImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1301_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1362_ctorMatch), RAST.Expr.create_Block(_1366_hashRhs))));
        _1359_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1359_coerceImplBodyCases, Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1301_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), _1362_ctorMatch), RAST.Expr.create_Block(_1380_coerceRhs))));
      }
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        Dafny.ISequence<RAST._IMatchCase> _1381_extraCases;
        _1381_extraCases = Dafny.Sequence<RAST._IMatchCase>.FromElements(RAST.MatchCase.create(Dafny.Sequence<Dafny.Rune>.Concat(_1301_datatypeName, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::_PhantomVariant(..)")), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{panic!()}"))));
        _1357_printImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1357_printImplBodyCases, _1381_extraCases);
        _1358_hashImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1358_hashImplBodyCases, _1381_extraCases);
        _1359_coerceImplBodyCases = Dafny.Sequence<RAST._IMatchCase>.Concat(_1359_coerceImplBodyCases, _1381_extraCases);
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1382_defaultConstrainedTypeParams;
      _1382_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1299_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
      Dafny.ISequence<RAST._ITypeParamDecl> _1383_rTypeParamsDeclsWithEq;
      _1383_rTypeParamsDeclsWithEq = RAST.TypeParamDecl.AddConstraintsMultiple(_1299_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Eq));
      Dafny.ISequence<RAST._ITypeParamDecl> _1384_rTypeParamsDeclsWithHash;
      _1384_rTypeParamsDeclsWithHash = RAST.TypeParamDecl.AddConstraintsMultiple(_1299_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.Hash));
      RAST._IExpr _1385_printImplBody;
      _1385_printImplBody = RAST.Expr.create_Match(RAST.__default.self, _1357_printImplBodyCases);
      RAST._IExpr _1386_hashImplBody;
      _1386_hashImplBody = RAST.Expr.create_Match(RAST.__default.self, _1358_hashImplBodyCases);
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1299_rTypeParamsDecls, ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Debug")), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter"))))), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrint"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.__default.self, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("f")), RAST.Expr.create_LiteralBool(true))))))))), RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1299_rTypeParamsDecls, RAST.__default.DafnyPrint, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt_print"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_formatter"), RAST.Type.create_BorrowedMut(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("fmt"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Formatter")))), RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_in_seq"), RAST.Type.create_Bool())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("std::fmt::Result"))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1385_printImplBody))))))));
      if ((new BigInteger(((c).dtor_typeParams).Count)).Sign == 1) {
        RAST._IExpr _1387_coerceImplBody;
        _1387_coerceImplBody = RAST.Expr.create_Match(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), _1359_coerceImplBodyCases);
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_Impl(_1299_rTypeParamsDecls, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PUB(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"), _1337_rCoerceTypeParams, _1338_coerceArguments, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.__default.Rc(RAST.Type.create_ImplType(RAST.Type.create_FnType(Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams)), RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1336_coerceTypes))))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.RcNew(RAST.Expr.create_Lambda(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"), RAST.Type.create_SelfOwned())), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1336_coerceTypes)), _1387_coerceImplBody))))))))));
      }
      if (_1356_cIsEq) {
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1383_rTypeParamsDeclsWithEq, RAST.__default.Eq, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements()))));
      }
      s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1384_rTypeParamsDeclsWithHash, RAST.__default.Hash, RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(RAST.TypeParamDecl.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"), Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("hash"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Hasher"))))), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed, RAST.Formal.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_state"), RAST.Type.create_BorrowedMut(RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_H"))))), Std.Wrappers.Option<RAST._IType>.create_None(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1386_hashImplBody))))))));
      if ((new BigInteger(((c).dtor_ctors).Count)).Sign == 1) {
        RAST._IExpr _1388_structName;
        _1388_structName = (RAST.Expr.create_Identifier(_1301_datatypeName)).MSel(DCOMP.__default.escapeName((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_name));
        Dafny.ISequence<RAST._IAssignIdentifier> _1389_structAssignments;
        _1389_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
        BigInteger _hi21 = new BigInteger(((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Count);
        for (BigInteger _1390_i = BigInteger.Zero; _1390_i < _hi21; _1390_i++) {
          DAST._IDatatypeDtor _1391_dtor;
          _1391_dtor = ((((c).dtor_ctors).Select(BigInteger.Zero)).dtor_args).Select(_1390_i);
          _1389_structAssignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1389_structAssignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeName(((_1391_dtor).dtor_formal).dtor_name), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::default::Default::default()")))));
        }
        Dafny.ISequence<RAST._ITypeParamDecl> _1392_defaultConstrainedTypeParams;
        _1392_defaultConstrainedTypeParams = RAST.TypeParamDecl.AddConstraintsMultiple(_1299_rTypeParamsDecls, Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.DefaultTrait));
        RAST._IType _1393_fullType;
        _1393_fullType = RAST.Type.create_TypeApp(RAST.Type.create_TIdentifier(_1301_datatypeName), _1298_rTypeParams);
        if (_1356_cIsEq) {
          s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1392_defaultConstrainedTypeParams, RAST.__default.DefaultTrait, _1393_fullType, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(), Std.Wrappers.Option<RAST._IType>.create_Some(_1393_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_StructBuild(_1388_structName, _1389_structAssignments)))))))));
        }
        s = Dafny.Sequence<RAST._IModDecl>.Concat(s, Dafny.Sequence<RAST._IModDecl>.FromElements(RAST.ModDecl.create_ImplDecl(RAST.Impl.create_ImplFor(_1299_rTypeParamsDecls, (((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("convert"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("AsRef"))).Apply1(_1393_fullType), RAST.Type.create_Borrowed(_1393_fullType), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Dafny.Sequence<RAST._IImplMember>.FromElements(RAST.ImplMember.create_FnDecl(RAST.Visibility.create_PRIV(), RAST.Fn.create(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"), Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(), Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.selfBorrowed), Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_SelfOwned()), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.__default.self))))))));
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
        for (BigInteger _1394_i = BigInteger.Zero; _1394_i < _hi22; _1394_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1394_i))));
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
        for (BigInteger _1395_i = BigInteger.Zero; _1395_i < _hi23; _1395_i++) {
          r = (r).MSel(DCOMP.__default.escapeName(((p).Select(_1395_i))));
        }
      }
      return r;
    }
    public Dafny.ISequence<RAST._IType> GenTypeArgs(Dafny.ISequence<DAST._IType> args, DCOMP._IGenTypeContext genTypeContext)
    {
      Dafny.ISequence<RAST._IType> s = Dafny.Sequence<RAST._IType>.Empty;
      s = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi24 = new BigInteger((args).Count);
      for (BigInteger _1396_i = BigInteger.Zero; _1396_i < _hi24; _1396_i++) {
        RAST._IType _1397_genTp;
        RAST._IType _out85;
        _out85 = (this).GenType((args).Select(_1396_i), genTypeContext);
        _1397_genTp = _out85;
        s = Dafny.Sequence<RAST._IType>.Concat(s, Dafny.Sequence<RAST._IType>.FromElements(_1397_genTp));
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
          DAST._IResolvedType _1398_resolved = _source61.dtor_resolved;
          unmatched61 = false;
          {
            RAST._IType _1399_t;
            RAST._IType _out86;
            _out86 = DCOMP.COMP.GenPath((_1398_resolved).dtor_path);
            _1399_t = _out86;
            Dafny.ISequence<RAST._IType> _1400_typeArgs;
            Dafny.ISequence<RAST._IType> _out87;
            _out87 = (this).GenTypeArgs((_1398_resolved).dtor_typeArgs, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let11_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let11_0, _1401_dt__update__tmp_h0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let12_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let12_0, _1402_dt__update_hforTraitParents_h0 => DCOMP.GenTypeContext.create((_1401_dt__update__tmp_h0).dtor_inBinding, (_1401_dt__update__tmp_h0).dtor_inFn, _1402_dt__update_hforTraitParents_h0))))));
            _1400_typeArgs = _out87;
            s = RAST.Type.create_TypeApp(_1399_t, _1400_typeArgs);
            DAST._IResolvedTypeBase _source62 = (_1398_resolved).dtor_kind;
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
                unmatched62 = false;
                {
                  if ((this).IsRcWrapped((_1398_resolved).dtor_attributes)) {
                    s = RAST.__default.Rc(s);
                  }
                }
              }
            }
            if (unmatched62) {
              if (_source62.is_Trait) {
                unmatched62 = false;
                {
                  if (((_1398_resolved).dtor_path).Equals(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_System"), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("object")))) {
                    s = ((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Any"));
                  }
                  if (!((genTypeContext).dtor_forTraitParents)) {
                    s = (this).Object(RAST.Type.create_DynType(s));
                  }
                }
              }
            }
            if (unmatched62) {
              DAST._IType _1403_t = _source62.dtor_baseType;
              DAST._INewtypeRange _1404_range = _source62.dtor_range;
              bool _1405_erased = _source62.dtor_erase;
              unmatched62 = false;
              {
                if (_1405_erased) {
                  Std.Wrappers._IOption<RAST._IType> _source63 = DCOMP.COMP.NewtypeToRustType(_1403_t, _1404_range);
                  bool unmatched63 = true;
                  if (unmatched63) {
                    if (_source63.is_Some) {
                      RAST._IType _1406_v = _source63.dtor_value;
                      unmatched63 = false;
                      s = _1406_v;
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
          Dafny.ISequence<DAST._IType> _1407_types = _source61.dtor_Tuple_a0;
          unmatched61 = false;
          {
            Dafny.ISequence<RAST._IType> _1408_args;
            _1408_args = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1409_i;
            _1409_i = BigInteger.Zero;
            while ((_1409_i) < (new BigInteger((_1407_types).Count))) {
              RAST._IType _1410_generated;
              RAST._IType _out88;
              _out88 = (this).GenType((_1407_types).Select(_1409_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let13_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let13_0, _1411_dt__update__tmp_h1 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let14_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let14_0, _1412_dt__update_hforTraitParents_h1 => DCOMP.GenTypeContext.create((_1411_dt__update__tmp_h1).dtor_inBinding, (_1411_dt__update__tmp_h1).dtor_inFn, _1412_dt__update_hforTraitParents_h1))))));
              _1410_generated = _out88;
              _1408_args = Dafny.Sequence<RAST._IType>.Concat(_1408_args, Dafny.Sequence<RAST._IType>.FromElements(_1410_generated));
              _1409_i = (_1409_i) + (BigInteger.One);
            }
            s = (((new BigInteger((_1407_types).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Type.create_TupleType(_1408_args)) : (RAST.__default.SystemTupleType(_1408_args)));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Array) {
          DAST._IType _1413_element = _source61.dtor_element;
          BigInteger _1414_dims = _source61.dtor_dims;
          unmatched61 = false;
          {
            if ((_1414_dims) > (new BigInteger(16))) {
              s = RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<i>Array of dimensions greater than 16</i>"));
            } else {
              RAST._IType _1415_elem;
              RAST._IType _out89;
              _out89 = (this).GenType(_1413_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let15_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let15_0, _1416_dt__update__tmp_h2 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let16_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let16_0, _1417_dt__update_hforTraitParents_h2 => DCOMP.GenTypeContext.create((_1416_dt__update__tmp_h2).dtor_inBinding, (_1416_dt__update__tmp_h2).dtor_inFn, _1417_dt__update_hforTraitParents_h2))))));
              _1415_elem = _out89;
              if ((_1414_dims) == (BigInteger.One)) {
                s = RAST.Type.create_Array(_1415_elem, Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None());
                s = (this).Object(s);
              } else {
                Dafny.ISequence<Dafny.Rune> _1418_n;
                _1418_n = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(_1414_dims));
                s = ((RAST.__default.dafny__runtime__type).MSel(_1418_n)).Apply(Dafny.Sequence<RAST._IType>.FromElements(_1415_elem));
                s = (this).Object(s);
              }
            }
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Seq) {
          DAST._IType _1419_element = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1420_elem;
            RAST._IType _out90;
            _out90 = (this).GenType(_1419_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let17_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let17_0, _1421_dt__update__tmp_h3 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let18_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let18_0, _1422_dt__update_hforTraitParents_h3 => DCOMP.GenTypeContext.create((_1421_dt__update__tmp_h3).dtor_inBinding, (_1421_dt__update__tmp_h3).dtor_inFn, _1422_dt__update_hforTraitParents_h3))))));
            _1420_elem = _out90;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence")), Dafny.Sequence<RAST._IType>.FromElements(_1420_elem));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Set) {
          DAST._IType _1423_element = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1424_elem;
            RAST._IType _out91;
            _out91 = (this).GenType(_1423_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let19_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let19_0, _1425_dt__update__tmp_h4 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let20_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let20_0, _1426_dt__update_hforTraitParents_h4 => DCOMP.GenTypeContext.create((_1425_dt__update__tmp_h4).dtor_inBinding, (_1425_dt__update__tmp_h4).dtor_inFn, _1426_dt__update_hforTraitParents_h4))))));
            _1424_elem = _out91;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Set")), Dafny.Sequence<RAST._IType>.FromElements(_1424_elem));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Multiset) {
          DAST._IType _1427_element = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1428_elem;
            RAST._IType _out92;
            _out92 = (this).GenType(_1427_element, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let21_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let21_0, _1429_dt__update__tmp_h5 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let22_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let22_0, _1430_dt__update_hforTraitParents_h5 => DCOMP.GenTypeContext.create((_1429_dt__update__tmp_h5).dtor_inBinding, (_1429_dt__update__tmp_h5).dtor_inFn, _1430_dt__update_hforTraitParents_h5))))));
            _1428_elem = _out92;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Multiset")), Dafny.Sequence<RAST._IType>.FromElements(_1428_elem));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Map) {
          DAST._IType _1431_key = _source61.dtor_key;
          DAST._IType _1432_value = _source61.dtor_value;
          unmatched61 = false;
          {
            RAST._IType _1433_keyType;
            RAST._IType _out93;
            _out93 = (this).GenType(_1431_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let23_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let23_0, _1434_dt__update__tmp_h6 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let24_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let24_0, _1435_dt__update_hforTraitParents_h6 => DCOMP.GenTypeContext.create((_1434_dt__update__tmp_h6).dtor_inBinding, (_1434_dt__update__tmp_h6).dtor_inFn, _1435_dt__update_hforTraitParents_h6))))));
            _1433_keyType = _out93;
            RAST._IType _1436_valueType;
            RAST._IType _out94;
            _out94 = (this).GenType(_1432_value, genTypeContext);
            _1436_valueType = _out94;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map")), Dafny.Sequence<RAST._IType>.FromElements(_1433_keyType, _1436_valueType));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_MapBuilder) {
          DAST._IType _1437_key = _source61.dtor_key;
          DAST._IType _1438_value = _source61.dtor_value;
          unmatched61 = false;
          {
            RAST._IType _1439_keyType;
            RAST._IType _out95;
            _out95 = (this).GenType(_1437_key, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let25_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let25_0, _1440_dt__update__tmp_h7 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let26_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let26_0, _1441_dt__update_hforTraitParents_h7 => DCOMP.GenTypeContext.create((_1440_dt__update__tmp_h7).dtor_inBinding, (_1440_dt__update__tmp_h7).dtor_inFn, _1441_dt__update_hforTraitParents_h7))))));
            _1439_keyType = _out95;
            RAST._IType _1442_valueType;
            RAST._IType _out96;
            _out96 = (this).GenType(_1438_value, genTypeContext);
            _1442_valueType = _out96;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1439_keyType, _1442_valueType));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_SetBuilder) {
          DAST._IType _1443_elem = _source61.dtor_element;
          unmatched61 = false;
          {
            RAST._IType _1444_elemType;
            RAST._IType _out97;
            _out97 = (this).GenType(_1443_elem, Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let27_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let27_0, _1445_dt__update__tmp_h8 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let28_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let28_0, _1446_dt__update_hforTraitParents_h8 => DCOMP.GenTypeContext.create((_1445_dt__update__tmp_h8).dtor_inBinding, (_1445_dt__update__tmp_h8).dtor_inFn, _1446_dt__update_hforTraitParents_h8))))));
            _1444_elemType = _out97;
            s = RAST.Type.create_TypeApp((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder")), Dafny.Sequence<RAST._IType>.FromElements(_1444_elemType));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_Arrow) {
          Dafny.ISequence<DAST._IType> _1447_args = _source61.dtor_args;
          DAST._IType _1448_result = _source61.dtor_result;
          unmatched61 = false;
          {
            Dafny.ISequence<RAST._IType> _1449_argTypes;
            _1449_argTypes = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _1450_i;
            _1450_i = BigInteger.Zero;
            while ((_1450_i) < (new BigInteger((_1447_args).Count))) {
              RAST._IType _1451_generated;
              RAST._IType _out98;
              _out98 = (this).GenType((_1447_args).Select(_1450_i), Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(genTypeContext, _pat_let29_0 => Dafny.Helpers.Let<DCOMP._IGenTypeContext, DCOMP._IGenTypeContext>(_pat_let29_0, _1452_dt__update__tmp_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(false, _pat_let30_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let30_0, _1453_dt__update_hforTraitParents_h9 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(true, _pat_let31_0 => Dafny.Helpers.Let<bool, DCOMP._IGenTypeContext>(_pat_let31_0, _1454_dt__update_hinFn_h0 => DCOMP.GenTypeContext.create((_1452_dt__update__tmp_h9).dtor_inBinding, _1454_dt__update_hinFn_h0, _1453_dt__update_hforTraitParents_h9))))))));
              _1451_generated = _out98;
              _1449_argTypes = Dafny.Sequence<RAST._IType>.Concat(_1449_argTypes, Dafny.Sequence<RAST._IType>.FromElements(RAST.Type.create_Borrowed(_1451_generated)));
              _1450_i = (_1450_i) + (BigInteger.One);
            }
            RAST._IType _1455_resultType;
            RAST._IType _out99;
            _out99 = (this).GenType(_1448_result, DCOMP.GenTypeContext.create(((genTypeContext).dtor_inFn) || ((genTypeContext).dtor_inBinding), false, false));
            _1455_resultType = _out99;
            s = RAST.__default.Rc(RAST.Type.create_DynType(RAST.Type.create_FnType(_1449_argTypes, _1455_resultType)));
          }
        }
      }
      if (unmatched61) {
        if (_source61.is_TypeArg) {
          Dafny.ISequence<Dafny.Rune> _h90 = _source61.dtor_TypeArg_a0;
          Dafny.ISequence<Dafny.Rune> _1456_name = _h90;
          unmatched61 = false;
          s = RAST.Type.create_TIdentifier(DCOMP.__default.escapeName(_1456_name));
        }
      }
      if (unmatched61) {
        if (_source61.is_Primitive) {
          DAST._IPrimitive _1457_p = _source61.dtor_Primitive_a0;
          unmatched61 = false;
          {
            DAST._IPrimitive _source64 = _1457_p;
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
        Dafny.ISequence<Dafny.Rune> _1458_v = _source61.dtor_Passthrough_a0;
        unmatched61 = false;
        s = RAST.__default.RawType(_1458_v);
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
      for (BigInteger _1459_i = BigInteger.Zero; _1459_i < _hi25; _1459_i++) {
        DAST._IMethod _source65 = (body).Select(_1459_i);
        bool unmatched65 = true;
        if (unmatched65) {
          DAST._IMethod _1460_m = _source65;
          unmatched65 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source66 = (_1460_m).dtor_overridingPath;
            bool unmatched66 = true;
            if (unmatched66) {
              if (_source66.is_Some) {
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1461_p = _source66.dtor_value;
                unmatched66 = false;
                {
                  Dafny.ISequence<RAST._IImplMember> _1462_existing;
                  _1462_existing = Dafny.Sequence<RAST._IImplMember>.FromElements();
                  if ((traitBodies).Contains(_1461_p)) {
                    _1462_existing = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Select(traitBodies,_1461_p);
                  }
                  if (((new BigInteger(((_1460_m).dtor_typeParams).Count)).Sign == 1) && ((this).EnclosingIsTrait(enclosingType))) {
                    (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Error: Rust does not support method with generic type parameters in traits"));
                  }
                  RAST._IImplMember _1463_genMethod;
                  RAST._IImplMember _out100;
                  _out100 = (this).GenMethod(_1460_m, true, enclosingType, enclosingTypeParams);
                  _1463_genMethod = _out100;
                  _1462_existing = Dafny.Sequence<RAST._IImplMember>.Concat(_1462_existing, Dafny.Sequence<RAST._IImplMember>.FromElements(_1463_genMethod));
                  traitBodies = Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.Merge(traitBodies, Dafny.Map<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISequence<RAST._IImplMember>>(_1461_p, _1462_existing)));
                }
              }
            }
            if (unmatched66) {
              unmatched66 = false;
              {
                RAST._IImplMember _1464_generated;
                RAST._IImplMember _out101;
                _out101 = (this).GenMethod(_1460_m, forTrait, enclosingType, enclosingTypeParams);
                _1464_generated = _out101;
                s = Dafny.Sequence<RAST._IImplMember>.Concat(s, Dafny.Sequence<RAST._IImplMember>.FromElements(_1464_generated));
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
      for (BigInteger _1465_i = BigInteger.Zero; _1465_i < _hi26; _1465_i++) {
        DAST._IFormal _1466_param;
        _1466_param = (@params).Select(_1465_i);
        RAST._IType _1467_paramType;
        RAST._IType _out102;
        _out102 = (this).GenType((_1466_param).dtor_typ, DCOMP.GenTypeContext.@default());
        _1467_paramType = _out102;
        if ((!((_1467_paramType).CanReadWithoutClone())) && (!((_1466_param).dtor_attributes).Contains(DCOMP.__default.AttributeOwned))) {
          _1467_paramType = RAST.Type.create_Borrowed(_1467_paramType);
        }
        s = Dafny.Sequence<RAST._IFormal>.Concat(s, Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(DCOMP.__default.escapeName((_1466_param).dtor_name), _1467_paramType)));
      }
      return s;
    }
    public RAST._IImplMember GenMethod(DAST._IMethod m, bool forTrait, DAST._IType enclosingType, Dafny.ISequence<DAST._IType> enclosingTypeParams)
    {
      RAST._IImplMember s = RAST.ImplMember.Default();
      Dafny.ISequence<RAST._IFormal> _1468_params;
      Dafny.ISequence<RAST._IFormal> _out103;
      _out103 = (this).GenParams((m).dtor_params);
      _1468_params = _out103;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1469_paramNames;
      _1469_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1470_paramTypes;
      _1470_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      BigInteger _hi27 = new BigInteger(((m).dtor_params).Count);
      for (BigInteger _1471_paramI = BigInteger.Zero; _1471_paramI < _hi27; _1471_paramI++) {
        DAST._IFormal _1472_dafny__formal;
        _1472_dafny__formal = ((m).dtor_params).Select(_1471_paramI);
        RAST._IFormal _1473_formal;
        _1473_formal = (_1468_params).Select(_1471_paramI);
        Dafny.ISequence<Dafny.Rune> _1474_name;
        _1474_name = (_1473_formal).dtor_name;
        _1469_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1469_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1474_name));
        _1470_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1470_paramTypes, _1474_name, (_1473_formal).dtor_tpe);
      }
      Dafny.ISequence<Dafny.Rune> _1475_fnName;
      _1475_fnName = DCOMP.__default.escapeName((m).dtor_name);
      DCOMP._ISelfInfo _1476_selfIdent;
      _1476_selfIdent = DCOMP.SelfInfo.create_NoSelf();
      if (!((m).dtor_isStatic)) {
        Dafny.ISequence<Dafny.Rune> _1477_selfId;
        _1477_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self");
        if ((_1475_fnName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_ctor"))) {
          _1477_selfId = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this");
        }
        var _pat_let_tv137 = enclosingTypeParams;
        var _pat_let_tv138 = enclosingType;
        DAST._IType _1478_instanceType;
        _1478_instanceType = ((System.Func<DAST._IType>)(() => {
          DAST._IType _source67 = enclosingType;
          bool unmatched67 = true;
          if (unmatched67) {
            if (_source67.is_UserDefined) {
              DAST._IResolvedType _1479_r = _source67.dtor_resolved;
              unmatched67 = false;
              return DAST.Type.create_UserDefined(Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_1479_r, _pat_let32_0 => Dafny.Helpers.Let<DAST._IResolvedType, DAST._IResolvedType>(_pat_let32_0, _1480_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let_tv137, _pat_let33_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IType>, DAST._IResolvedType>(_pat_let33_0, _1481_dt__update_htypeArgs_h0 => DAST.ResolvedType.create((_1480_dt__update__tmp_h0).dtor_path, _1481_dt__update_htypeArgs_h0, (_1480_dt__update__tmp_h0).dtor_kind, (_1480_dt__update__tmp_h0).dtor_attributes, (_1480_dt__update__tmp_h0).dtor_properMethods, (_1480_dt__update__tmp_h0).dtor_extendedTypes))))));
            }
          }
          if (unmatched67) {
            DAST._IType _1482___v67 = _source67;
            unmatched67 = false;
            return _pat_let_tv138;
          }
          throw new System.Exception("unexpected control point");
        }))();
        if (forTrait) {
          RAST._IFormal _1483_selfFormal;
          _1483_selfFormal = (((m).dtor_wasFunction) ? (RAST.Formal.selfBorrowed) : (RAST.Formal.selfBorrowedMut));
          _1468_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(_1483_selfFormal), _1468_params);
        } else {
          RAST._IType _1484_tpe;
          RAST._IType _out104;
          _out104 = (this).GenType(_1478_instanceType, DCOMP.GenTypeContext.@default());
          _1484_tpe = _out104;
          if ((_1477_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
            _1484_tpe = RAST.Type.create_Borrowed(_1484_tpe);
          } else if ((_1477_selfId).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
            if ((_1484_tpe).IsObjectOrPointer()) {
              if ((m).dtor_wasFunction) {
                _1484_tpe = RAST.__default.SelfBorrowed;
              } else {
                _1484_tpe = RAST.__default.SelfBorrowedMut;
              }
            } else {
              _1484_tpe = RAST.Type.create_Borrowed(RAST.__default.Rc(RAST.Type.create_SelfOwned()));
            }
          }
          _1468_params = Dafny.Sequence<RAST._IFormal>.Concat(Dafny.Sequence<RAST._IFormal>.FromElements(RAST.Formal.create(_1477_selfId, _1484_tpe)), _1468_params);
        }
        _1476_selfIdent = DCOMP.SelfInfo.create_ThisTyped(_1477_selfId, _1478_instanceType);
      }
      Dafny.ISequence<RAST._IType> _1485_retTypeArgs;
      _1485_retTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _1486_typeI;
      _1486_typeI = BigInteger.Zero;
      while ((_1486_typeI) < (new BigInteger(((m).dtor_outTypes).Count))) {
        RAST._IType _1487_typeExpr;
        RAST._IType _out105;
        _out105 = (this).GenType(((m).dtor_outTypes).Select(_1486_typeI), DCOMP.GenTypeContext.@default());
        _1487_typeExpr = _out105;
        _1485_retTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1485_retTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1487_typeExpr));
        _1486_typeI = (_1486_typeI) + (BigInteger.One);
      }
      RAST._IVisibility _1488_visibility;
      _1488_visibility = ((forTrait) ? (RAST.Visibility.create_PRIV()) : (RAST.Visibility.create_PUB()));
      Dafny.ISequence<DAST._ITypeArgDecl> _1489_typeParamsFiltered;
      _1489_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.FromElements();
      BigInteger _hi28 = new BigInteger(((m).dtor_typeParams).Count);
      for (BigInteger _1490_typeParamI = BigInteger.Zero; _1490_typeParamI < _hi28; _1490_typeParamI++) {
        DAST._ITypeArgDecl _1491_typeParam;
        _1491_typeParam = ((m).dtor_typeParams).Select(_1490_typeParamI);
        if (!((enclosingTypeParams).Contains(DAST.Type.create_TypeArg((_1491_typeParam).dtor_name)))) {
          _1489_typeParamsFiltered = Dafny.Sequence<DAST._ITypeArgDecl>.Concat(_1489_typeParamsFiltered, Dafny.Sequence<DAST._ITypeArgDecl>.FromElements(_1491_typeParam));
        }
      }
      Dafny.ISequence<RAST._ITypeParamDecl> _1492_typeParams;
      _1492_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.FromElements();
      if ((new BigInteger((_1489_typeParamsFiltered).Count)).Sign == 1) {
        BigInteger _hi29 = new BigInteger((_1489_typeParamsFiltered).Count);
        for (BigInteger _1493_i = BigInteger.Zero; _1493_i < _hi29; _1493_i++) {
          DAST._IType _1494_typeArg;
          RAST._ITypeParamDecl _1495_rTypeParamDecl;
          DAST._IType _out106;
          RAST._ITypeParamDecl _out107;
          (this).GenTypeParam((_1489_typeParamsFiltered).Select(_1493_i), out _out106, out _out107);
          _1494_typeArg = _out106;
          _1495_rTypeParamDecl = _out107;
          var _pat_let_tv139 = _1495_rTypeParamDecl;
          _1495_rTypeParamDecl = Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_1495_rTypeParamDecl, _pat_let34_0 => Dafny.Helpers.Let<RAST._ITypeParamDecl, RAST._ITypeParamDecl>(_pat_let34_0, _1496_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(Dafny.Sequence<RAST._IType>.Concat((_pat_let_tv139).dtor_constraints, Dafny.Sequence<RAST._IType>.FromElements(((RAST.__default.std__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("default"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Default")))), _pat_let35_0 => Dafny.Helpers.Let<Dafny.ISequence<RAST._IType>, RAST._ITypeParamDecl>(_pat_let35_0, _1497_dt__update_hconstraints_h0 => RAST.TypeParamDecl.create((_1496_dt__update__tmp_h1).dtor_content, _1497_dt__update_hconstraints_h0)))));
          _1492_typeParams = Dafny.Sequence<RAST._ITypeParamDecl>.Concat(_1492_typeParams, Dafny.Sequence<RAST._ITypeParamDecl>.FromElements(_1495_rTypeParamDecl));
        }
      }
      Std.Wrappers._IOption<RAST._IExpr> _1498_fBody = Std.Wrappers.Option<RAST._IExpr>.Default();
      DCOMP._IEnvironment _1499_env = DCOMP.Environment.Default();
      RAST._IExpr _1500_preBody;
      _1500_preBody = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1501_preAssignNames;
      _1501_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
      Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _1502_preAssignTypes;
      _1502_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
      if ((m).dtor_hasBody) {
        RAST._IExpr _1503_earlyReturn;
        _1503_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_None());
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _source68 = (m).dtor_outVars;
        bool unmatched68 = true;
        if (unmatched68) {
          if (_source68.is_Some) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1504_outVars = _source68.dtor_value;
            unmatched68 = false;
            {
              if ((m).dtor_outVarsAreUninitFieldsToAssign) {
                _1503_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(Dafny.Sequence<RAST._IExpr>.FromElements())));
                BigInteger _hi30 = new BigInteger((_1504_outVars).Count);
                for (BigInteger _1505_outI = BigInteger.Zero; _1505_outI < _hi30; _1505_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1506_outVar;
                  _1506_outVar = (_1504_outVars).Select(_1505_outI);
                  Dafny.ISequence<Dafny.Rune> _1507_outName;
                  _1507_outName = DCOMP.__default.escapeName((_1506_outVar));
                  Dafny.ISequence<Dafny.Rune> _1508_tracker__name;
                  _1508_tracker__name = DCOMP.__default.AddAssignedPrefix(_1507_outName);
                  _1501_preAssignNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1501_preAssignNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1508_tracker__name));
                  _1502_preAssignTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1502_preAssignTypes, _1508_tracker__name, RAST.Type.create_Bool());
                  _1500_preBody = (_1500_preBody).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1508_tracker__name, Std.Wrappers.Option<RAST._IType>.create_Some(RAST.Type.create_Bool()), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_LiteralBool(false))));
                }
              } else {
                Dafny.ISequence<RAST._IExpr> _1509_tupleArgs;
                _1509_tupleArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
                BigInteger _hi31 = new BigInteger((_1504_outVars).Count);
                for (BigInteger _1510_outI = BigInteger.Zero; _1510_outI < _hi31; _1510_outI++) {
                  Dafny.ISequence<Dafny.Rune> _1511_outVar;
                  _1511_outVar = (_1504_outVars).Select(_1510_outI);
                  RAST._IType _1512_outType;
                  RAST._IType _out108;
                  _out108 = (this).GenType(((m).dtor_outTypes).Select(_1510_outI), DCOMP.GenTypeContext.@default());
                  _1512_outType = _out108;
                  Dafny.ISequence<Dafny.Rune> _1513_outName;
                  _1513_outName = DCOMP.__default.escapeName((_1511_outVar));
                  _1469_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1469_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1513_outName));
                  RAST._IType _1514_outMaybeType;
                  _1514_outMaybeType = (((_1512_outType).CanReadWithoutClone()) ? (_1512_outType) : (RAST.__default.MaybePlaceboType(_1512_outType)));
                  _1470_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_1470_paramTypes, _1513_outName, _1514_outMaybeType);
                  RAST._IExpr _1515_outVarReturn;
                  DCOMP._IOwnership _1516___v68;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1517___v69;
                  RAST._IExpr _out109;
                  DCOMP._IOwnership _out110;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out111;
                  (this).GenExpr(DAST.Expression.create_Ident((_1511_outVar)), DCOMP.SelfInfo.create_NoSelf(), DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_1513_outName), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements(new Dafny.Pair<Dafny.ISequence<Dafny.Rune>, RAST._IType>(_1513_outName, _1514_outMaybeType))), DCOMP.Ownership.create_OwnershipOwned(), out _out109, out _out110, out _out111);
                  _1515_outVarReturn = _out109;
                  _1516___v68 = _out110;
                  _1517___v69 = _out111;
                  _1509_tupleArgs = Dafny.Sequence<RAST._IExpr>.Concat(_1509_tupleArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_1515_outVarReturn));
                }
                if ((new BigInteger((_1509_tupleArgs).Count)) == (BigInteger.One)) {
                  _1503_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some((_1509_tupleArgs).Select(BigInteger.Zero)));
                } else {
                  _1503_earlyReturn = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_Tuple(_1509_tupleArgs)));
                }
              }
            }
          }
        }
        if (unmatched68) {
          unmatched68 = false;
        }
        _1499_env = DCOMP.Environment.create(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_1501_preAssignNames, _1469_paramNames), Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Merge(_1502_preAssignTypes, _1470_paramTypes));
        RAST._IExpr _1518_body;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1519___v70;
        DCOMP._IEnvironment _1520___v71;
        RAST._IExpr _out112;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out113;
        DCOMP._IEnvironment _out114;
        (this).GenStmts((m).dtor_body, _1476_selfIdent, _1499_env, true, _1503_earlyReturn, out _out112, out _out113, out _out114);
        _1518_body = _out112;
        _1519___v70 = _out113;
        _1520___v71 = _out114;
        _1498_fBody = Std.Wrappers.Option<RAST._IExpr>.create_Some((_1500_preBody).Then(_1518_body));
      } else {
        _1499_env = DCOMP.Environment.create(_1469_paramNames, _1470_paramTypes);
        _1498_fBody = Std.Wrappers.Option<RAST._IExpr>.create_None();
      }
      s = RAST.ImplMember.create_FnDecl(_1488_visibility, RAST.Fn.create(_1475_fnName, _1492_typeParams, _1468_params, Std.Wrappers.Option<RAST._IType>.create_Some((((new BigInteger((_1485_retTypeArgs).Count)) == (BigInteger.One)) ? ((_1485_retTypeArgs).Select(BigInteger.Zero)) : (RAST.Type.create_TupleType(_1485_retTypeArgs)))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""), _1498_fBody));
      return s;
    }
    public void GenStmts(Dafny.ISequence<DAST._IStatement> stmts, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, bool isLast, RAST._IExpr earlyReturn, out RAST._IExpr generated, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents, out DCOMP._IEnvironment newEnv)
    {
      generated = RAST.Expr.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      newEnv = DCOMP.Environment.Default();
      generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1521_declarations;
      _1521_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
      BigInteger _1522_i;
      _1522_i = BigInteger.Zero;
      newEnv = env;
      Dafny.ISequence<DAST._IStatement> _1523_stmts;
      _1523_stmts = stmts;
      while ((_1522_i) < (new BigInteger((_1523_stmts).Count))) {
        DAST._IStatement _1524_stmt;
        _1524_stmt = (_1523_stmts).Select(_1522_i);
        DAST._IStatement _source69 = _1524_stmt;
        bool unmatched69 = true;
        if (unmatched69) {
          if (_source69.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1525_name = _source69.dtor_name;
            DAST._IType _1526_optType = _source69.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> maybeValue0 = _source69.dtor_maybeValue;
            if (maybeValue0.is_None) {
              unmatched69 = false;
              if (((_1522_i) + (BigInteger.One)) < (new BigInteger((_1523_stmts).Count))) {
                DAST._IStatement _source70 = (_1523_stmts).Select((_1522_i) + (BigInteger.One));
                bool unmatched70 = true;
                if (unmatched70) {
                  if (_source70.is_Assign) {
                    DAST._IAssignLhs lhs0 = _source70.dtor_lhs;
                    if (lhs0.is_Ident) {
                      Dafny.ISequence<Dafny.Rune> ident0 = lhs0.dtor_ident;
                      Dafny.ISequence<Dafny.Rune> _1527_name2 = ident0;
                      DAST._IExpression _1528_rhs = _source70.dtor_value;
                      unmatched70 = false;
                      if (object.Equals(_1527_name2, _1525_name)) {
                        _1523_stmts = Dafny.Sequence<DAST._IStatement>.Concat(Dafny.Sequence<DAST._IStatement>.Concat((_1523_stmts).Subsequence(BigInteger.Zero, _1522_i), Dafny.Sequence<DAST._IStatement>.FromElements(DAST.Statement.create_DeclareVar(_1525_name, _1526_optType, Std.Wrappers.Option<DAST._IExpression>.create_Some(_1528_rhs)))), (_1523_stmts).Drop((_1522_i) + (new BigInteger(2))));
                        _1524_stmt = (_1523_stmts).Select(_1522_i);
                      }
                    }
                  }
                }
                if (unmatched70) {
                  DAST._IStatement _1529___v72 = _source70;
                  unmatched70 = false;
                }
              }
            }
          }
        }
        if (unmatched69) {
          DAST._IStatement _1530___v73 = _source69;
          unmatched69 = false;
        }
        RAST._IExpr _1531_stmtExpr;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1532_recIdents;
        DCOMP._IEnvironment _1533_newEnv2;
        RAST._IExpr _out115;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out116;
        DCOMP._IEnvironment _out117;
        (this).GenStmt(_1524_stmt, selfIdent, newEnv, (isLast) && ((_1522_i) == ((new BigInteger((_1523_stmts).Count)) - (BigInteger.One))), earlyReturn, out _out115, out _out116, out _out117);
        _1531_stmtExpr = _out115;
        _1532_recIdents = _out116;
        _1533_newEnv2 = _out117;
        newEnv = _1533_newEnv2;
        DAST._IStatement _source71 = _1524_stmt;
        bool unmatched71 = true;
        if (unmatched71) {
          if (_source71.is_DeclareVar) {
            Dafny.ISequence<Dafny.Rune> _1534_name = _source71.dtor_name;
            DAST._IType _1535___v74 = _source71.dtor_typ;
            Std.Wrappers._IOption<DAST._IExpression> _1536___v75 = _source71.dtor_maybeValue;
            unmatched71 = false;
            {
              _1521_declarations = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1521_declarations, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName(_1534_name)));
            }
          }
        }
        if (unmatched71) {
          DAST._IStatement _1537___v76 = _source71;
          unmatched71 = false;
        }
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1532_recIdents, _1521_declarations));
        generated = (generated).Then(_1531_stmtExpr);
        _1522_i = (_1522_i) + (BigInteger.One);
        if ((_1531_stmtExpr).is_Return) {
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
          Dafny.ISequence<Dafny.Rune> _1538_id = ident1;
          unmatched72 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1539_idRust;
            _1539_idRust = DCOMP.__default.escapeName(_1538_id);
            if (((env).IsBorrowed(_1539_idRust)) || ((env).IsBorrowedMut(_1539_idRust))) {
              generated = RAST.__default.AssignVar(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("*"), _1539_idRust), rhs);
            } else {
              generated = RAST.__default.AssignVar(_1539_idRust, rhs);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1539_idRust);
            needsIIFE = false;
          }
        }
      }
      if (unmatched72) {
        if (_source72.is_Select) {
          DAST._IExpression _1540_on = _source72.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _1541_field = _source72.dtor_field;
          unmatched72 = false;
          {
            Dafny.ISequence<Dafny.Rune> _1542_fieldName;
            _1542_fieldName = DCOMP.__default.escapeName(_1541_field);
            RAST._IExpr _1543_onExpr;
            DCOMP._IOwnership _1544_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1545_recIdents;
            RAST._IExpr _out118;
            DCOMP._IOwnership _out119;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out120;
            (this).GenExpr(_1540_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out118, out _out119, out _out120);
            _1543_onExpr = _out118;
            _1544_onOwned = _out119;
            _1545_recIdents = _out120;
            RAST._IExpr _source73 = _1543_onExpr;
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
                        Dafny.ISequence<RAST._IExpr> _1546___v77 = _source73.dtor_arguments;
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
                      DAST.Format._IUnaryOpFormat _1547___v78 = _source73.dtor_format;
                      disjunctiveMatch11 = true;
                    }
                  }
                }
              }
              if (disjunctiveMatch11) {
                unmatched73 = false;
                Dafny.ISequence<Dafny.Rune> _1548_isAssignedVar;
                _1548_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1542_fieldName);
                if (((newEnv).dtor_names).Contains(_1548_isAssignedVar)) {
                  generated = ((RAST.__default.dafny__runtime).MSel((this).update__field__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements((this).thisInConstructor, RAST.Expr.create_Identifier(_1542_fieldName), RAST.Expr.create_Identifier(_1548_isAssignedVar), rhs));
                  newEnv = (newEnv).RemoveAssigned(_1548_isAssignedVar);
                } else {
                  (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unespected field to assign whose isAssignedVar is not in the environment: "), _1548_isAssignedVar));
                  generated = RAST.__default.AssignMember(RAST.Expr.create_RawExpr((this.error).dtor_value), _1542_fieldName, rhs);
                }
              }
            }
            if (unmatched73) {
              RAST._IExpr _1549___v79 = _source73;
              unmatched73 = false;
              if (!object.Equals(_1543_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self")))) {
                _1543_onExpr = ((this).modify__macro).Apply1(_1543_onExpr);
              }
              generated = RAST.__default.AssignMember(_1543_onExpr, _1542_fieldName, rhs);
            }
            readIdents = _1545_recIdents;
            needsIIFE = false;
          }
        }
      }
      if (unmatched72) {
        DAST._IExpression _1550_on = _source72.dtor_expr;
        Dafny.ISequence<DAST._IExpression> _1551_indices = _source72.dtor_indices;
        unmatched72 = false;
        {
          RAST._IExpr _1552_onExpr;
          DCOMP._IOwnership _1553_onOwned;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1554_recIdents;
          RAST._IExpr _out121;
          DCOMP._IOwnership _out122;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out123;
          (this).GenExpr(_1550_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out121, out _out122, out _out123);
          _1552_onExpr = _out121;
          _1553_onOwned = _out122;
          _1554_recIdents = _out123;
          readIdents = _1554_recIdents;
          _1552_onExpr = ((this).modify__macro).Apply1(_1552_onExpr);
          RAST._IExpr _1555_r;
          _1555_r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
          Dafny.ISequence<RAST._IExpr> _1556_indicesExpr;
          _1556_indicesExpr = Dafny.Sequence<RAST._IExpr>.FromElements();
          BigInteger _hi32 = new BigInteger((_1551_indices).Count);
          for (BigInteger _1557_i = BigInteger.Zero; _1557_i < _hi32; _1557_i++) {
            RAST._IExpr _1558_idx;
            DCOMP._IOwnership _1559___v80;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1560_recIdentsIdx;
            RAST._IExpr _out124;
            DCOMP._IOwnership _out125;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out126;
            (this).GenExpr((_1551_indices).Select(_1557_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out124, out _out125, out _out126);
            _1558_idx = _out124;
            _1559___v80 = _out125;
            _1560_recIdentsIdx = _out126;
            Dafny.ISequence<Dafny.Rune> _1561_varName;
            _1561_varName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("__idx"), Std.Strings.__default.OfNat(_1557_i));
            _1556_indicesExpr = Dafny.Sequence<RAST._IExpr>.Concat(_1556_indicesExpr, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(_1561_varName)));
            _1555_r = (_1555_r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1561_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<usize as ::dafny_runtime::NumCast>::from("), (_1558_idx)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()"))))));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1560_recIdentsIdx);
          }
          if ((new BigInteger((_1551_indices).Count)) > (BigInteger.One)) {
            _1552_onExpr = (_1552_onExpr).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"));
          }
          RAST._IExpr _1562_rhs;
          _1562_rhs = rhs;
          var _pat_let_tv140 = env;
          if (((_1552_onExpr).IsLhsIdentifier()) && (Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>((_1552_onExpr).LhsIdentifierName(), _pat_let36_0 => Dafny.Helpers.Let<Dafny.ISequence<Dafny.Rune>, bool>(_pat_let36_0, _1563_name => (true) && (Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>((_pat_let_tv140).GetType(_1563_name), _pat_let37_0 => Dafny.Helpers.Let<Std.Wrappers._IOption<RAST._IType>, bool>(_pat_let37_0, _1564_tpe => ((_1564_tpe).is_Some) && (((_1564_tpe).dtor_value).IsUninitArray())))))))) {
            _1562_rhs = RAST.__default.MaybeUninitNew(_1562_rhs);
          }
          generated = (_1555_r).Then(RAST.Expr.create_Assign(Std.Wrappers.Option<RAST._IAssignLhs>.create_Some(RAST.AssignLhs.create_Index(_1552_onExpr, _1556_indicesExpr)), _1562_rhs));
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
          Dafny.ISequence<DAST._IFormal> _1565_fields = _source74.dtor_fields;
          unmatched74 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            newEnv = env;
            BigInteger _hi33 = new BigInteger((_1565_fields).Count);
            for (BigInteger _1566_i = BigInteger.Zero; _1566_i < _hi33; _1566_i++) {
              DAST._IFormal _1567_field;
              _1567_field = (_1565_fields).Select(_1566_i);
              Dafny.ISequence<Dafny.Rune> _1568_fieldName;
              _1568_fieldName = DCOMP.__default.escapeName((_1567_field).dtor_name);
              RAST._IType _1569_fieldTyp;
              RAST._IType _out127;
              _out127 = (this).GenType((_1567_field).dtor_typ, DCOMP.GenTypeContext.@default());
              _1569_fieldTyp = _out127;
              Dafny.ISequence<Dafny.Rune> _1570_isAssignedVar;
              _1570_isAssignedVar = DCOMP.__default.AddAssignedPrefix(_1568_fieldName);
              if (((newEnv).dtor_names).Contains(_1570_isAssignedVar)) {
                RAST._IExpr _1571_rhs;
                DCOMP._IOwnership _1572___v81;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1573___v82;
                RAST._IExpr _out128;
                DCOMP._IOwnership _out129;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out130;
                (this).GenExpr(DAST.Expression.create_InitializationValue((_1567_field).dtor_typ), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out128, out _out129, out _out130);
                _1571_rhs = _out128;
                _1572___v81 = _out129;
                _1573___v82 = _out130;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1570_isAssignedVar));
                generated = (generated).Then(((RAST.__default.dafny__runtime).MSel((this).update__field__if__uninit__macro)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this")), RAST.Expr.create_Identifier(_1568_fieldName), RAST.Expr.create_Identifier(_1570_isAssignedVar), _1571_rhs)));
                newEnv = (newEnv).RemoveAssigned(_1570_isAssignedVar);
              }
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1574_name = _source74.dtor_name;
          DAST._IType _1575_typ = _source74.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue1 = _source74.dtor_maybeValue;
          if (maybeValue1.is_Some) {
            DAST._IExpression _1576_expression = maybeValue1.dtor_value;
            unmatched74 = false;
            {
              RAST._IType _1577_tpe;
              RAST._IType _out131;
              _out131 = (this).GenType(_1575_typ, DCOMP.GenTypeContext.InBinding());
              _1577_tpe = _out131;
              Dafny.ISequence<Dafny.Rune> _1578_varName;
              _1578_varName = DCOMP.__default.escapeName(_1574_name);
              bool _1579_hasCopySemantics;
              _1579_hasCopySemantics = (_1577_tpe).CanReadWithoutClone();
              if (((_1576_expression).is_InitializationValue) && (!(_1579_hasCopySemantics))) {
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1578_varName, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MaybePlacebo"))).ApplyType1(_1577_tpe)).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                newEnv = (env).AddAssigned(_1578_varName, RAST.__default.MaybePlaceboType(_1577_tpe));
              } else {
                RAST._IExpr _1580_expr = RAST.Expr.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1581_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1576_expression).is_InitializationValue) && ((_1577_tpe).IsObjectOrPointer())) {
                  _1580_expr = (_1577_tpe).ToNullExpr();
                  _1581_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
                } else {
                  DCOMP._IOwnership _1582_exprOwnership = DCOMP.Ownership.Default();
                  RAST._IExpr _out132;
                  DCOMP._IOwnership _out133;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out134;
                  (this).GenExpr(_1576_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out132, out _out133, out _out134);
                  _1580_expr = _out132;
                  _1582_exprOwnership = _out133;
                  _1581_recIdents = _out134;
                }
                readIdents = _1581_recIdents;
                _1577_tpe = (((_1576_expression).is_NewUninitArray) ? ((_1577_tpe).TypeAtInitialization()) : (_1577_tpe));
                generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), DCOMP.__default.escapeName(_1574_name), Std.Wrappers.Option<RAST._IType>.create_Some(_1577_tpe), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1580_expr));
                newEnv = (env).AddAssigned(DCOMP.__default.escapeName(_1574_name), _1577_tpe);
              }
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_DeclareVar) {
          Dafny.ISequence<Dafny.Rune> _1583_name = _source74.dtor_name;
          DAST._IType _1584_typ = _source74.dtor_typ;
          Std.Wrappers._IOption<DAST._IExpression> maybeValue2 = _source74.dtor_maybeValue;
          if (maybeValue2.is_None) {
            unmatched74 = false;
            {
              DAST._IStatement _1585_newStmt;
              _1585_newStmt = DAST.Statement.create_DeclareVar(_1583_name, _1584_typ, Std.Wrappers.Option<DAST._IExpression>.create_Some(DAST.Expression.create_InitializationValue(_1584_typ)));
              RAST._IExpr _out135;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out136;
              DCOMP._IEnvironment _out137;
              (this).GenStmt(_1585_newStmt, selfIdent, env, isLast, earlyReturn, out _out135, out _out136, out _out137);
              generated = _out135;
              readIdents = _out136;
              newEnv = _out137;
            }
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Assign) {
          DAST._IAssignLhs _1586_lhs = _source74.dtor_lhs;
          DAST._IExpression _1587_expression = _source74.dtor_value;
          unmatched74 = false;
          {
            RAST._IExpr _1588_exprGen;
            DCOMP._IOwnership _1589___v83;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1590_exprIdents;
            RAST._IExpr _out138;
            DCOMP._IOwnership _out139;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out140;
            (this).GenExpr(_1587_expression, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out138, out _out139, out _out140);
            _1588_exprGen = _out138;
            _1589___v83 = _out139;
            _1590_exprIdents = _out140;
            if ((_1586_lhs).is_Ident) {
              Dafny.ISequence<Dafny.Rune> _1591_rustId;
              _1591_rustId = DCOMP.__default.escapeName(((_1586_lhs).dtor_ident));
              Std.Wrappers._IOption<RAST._IType> _1592_tpe;
              _1592_tpe = (env).GetType(_1591_rustId);
              if (((_1592_tpe).is_Some) && ((((_1592_tpe).dtor_value).ExtractMaybePlacebo()).is_Some)) {
                _1588_exprGen = RAST.__default.MaybePlacebo(_1588_exprGen);
              }
            }
            RAST._IExpr _1593_lhsGen;
            bool _1594_needsIIFE;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1595_recIdents;
            DCOMP._IEnvironment _1596_resEnv;
            RAST._IExpr _out141;
            bool _out142;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out143;
            DCOMP._IEnvironment _out144;
            (this).GenAssignLhs(_1586_lhs, _1588_exprGen, selfIdent, env, out _out141, out _out142, out _out143, out _out144);
            _1593_lhsGen = _out141;
            _1594_needsIIFE = _out142;
            _1595_recIdents = _out143;
            _1596_resEnv = _out144;
            generated = _1593_lhsGen;
            newEnv = _1596_resEnv;
            if (_1594_needsIIFE) {
              generated = RAST.Expr.create_Block(generated);
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1595_recIdents, _1590_exprIdents);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_If) {
          DAST._IExpression _1597_cond = _source74.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1598_thnDafny = _source74.dtor_thn;
          Dafny.ISequence<DAST._IStatement> _1599_elsDafny = _source74.dtor_els;
          unmatched74 = false;
          {
            RAST._IExpr _1600_cond;
            DCOMP._IOwnership _1601___v84;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1602_recIdents;
            RAST._IExpr _out145;
            DCOMP._IOwnership _out146;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out147;
            (this).GenExpr(_1597_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out145, out _out146, out _out147);
            _1600_cond = _out145;
            _1601___v84 = _out146;
            _1602_recIdents = _out147;
            Dafny.ISequence<Dafny.Rune> _1603_condString;
            _1603_condString = (_1600_cond)._ToString(DCOMP.__default.IND);
            readIdents = _1602_recIdents;
            RAST._IExpr _1604_thn;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1605_thnIdents;
            DCOMP._IEnvironment _1606_thnEnv;
            RAST._IExpr _out148;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out149;
            DCOMP._IEnvironment _out150;
            (this).GenStmts(_1598_thnDafny, selfIdent, env, isLast, earlyReturn, out _out148, out _out149, out _out150);
            _1604_thn = _out148;
            _1605_thnIdents = _out149;
            _1606_thnEnv = _out150;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1605_thnIdents);
            RAST._IExpr _1607_els;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1608_elsIdents;
            DCOMP._IEnvironment _1609_elsEnv;
            RAST._IExpr _out151;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out152;
            DCOMP._IEnvironment _out153;
            (this).GenStmts(_1599_elsDafny, selfIdent, env, isLast, earlyReturn, out _out151, out _out152, out _out153);
            _1607_els = _out151;
            _1608_elsIdents = _out152;
            _1609_elsEnv = _out153;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1608_elsIdents);
            newEnv = env;
            generated = RAST.Expr.create_IfExpr(_1600_cond, _1604_thn, _1607_els);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Labeled) {
          Dafny.ISequence<Dafny.Rune> _1610_lbl = _source74.dtor_lbl;
          Dafny.ISequence<DAST._IStatement> _1611_body = _source74.dtor_body;
          unmatched74 = false;
          {
            RAST._IExpr _1612_body;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1613_bodyIdents;
            DCOMP._IEnvironment _1614_env2;
            RAST._IExpr _out154;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out155;
            DCOMP._IEnvironment _out156;
            (this).GenStmts(_1611_body, selfIdent, env, isLast, earlyReturn, out _out154, out _out155, out _out156);
            _1612_body = _out154;
            _1613_bodyIdents = _out155;
            _1614_env2 = _out156;
            readIdents = _1613_bodyIdents;
            generated = RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1610_lbl), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), RAST.Expr.create_StmtExpr(_1612_body, RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None()))));
            newEnv = env;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_While) {
          DAST._IExpression _1615_cond = _source74.dtor_cond;
          Dafny.ISequence<DAST._IStatement> _1616_body = _source74.dtor_body;
          unmatched74 = false;
          {
            RAST._IExpr _1617_cond;
            DCOMP._IOwnership _1618___v85;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1619_recIdents;
            RAST._IExpr _out157;
            DCOMP._IOwnership _out158;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out159;
            (this).GenExpr(_1615_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out157, out _out158, out _out159);
            _1617_cond = _out157;
            _1618___v85 = _out158;
            _1619_recIdents = _out159;
            readIdents = _1619_recIdents;
            RAST._IExpr _1620_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1621_bodyIdents;
            DCOMP._IEnvironment _1622_bodyEnv;
            RAST._IExpr _out160;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out161;
            DCOMP._IEnvironment _out162;
            (this).GenStmts(_1616_body, selfIdent, env, false, earlyReturn, out _out160, out _out161, out _out162);
            _1620_bodyExpr = _out160;
            _1621_bodyIdents = _out161;
            _1622_bodyEnv = _out162;
            newEnv = env;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1621_bodyIdents);
            generated = RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1617_cond), _1620_bodyExpr);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Foreach) {
          Dafny.ISequence<Dafny.Rune> _1623_boundName = _source74.dtor_boundName;
          DAST._IType _1624_boundType = _source74.dtor_boundType;
          DAST._IExpression _1625_overExpr = _source74.dtor_over;
          Dafny.ISequence<DAST._IStatement> _1626_body = _source74.dtor_body;
          unmatched74 = false;
          {
            RAST._IExpr _1627_over;
            DCOMP._IOwnership _1628___v86;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1629_recIdents;
            RAST._IExpr _out163;
            DCOMP._IOwnership _out164;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out165;
            (this).GenExpr(_1625_overExpr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out163, out _out164, out _out165);
            _1627_over = _out163;
            _1628___v86 = _out164;
            _1629_recIdents = _out165;
            if (((_1625_overExpr).is_MapBoundedPool) || ((_1625_overExpr).is_SetBoundedPool)) {
              _1627_over = ((_1627_over).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cloned"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            }
            RAST._IType _1630_boundTpe;
            RAST._IType _out166;
            _out166 = (this).GenType(_1624_boundType, DCOMP.GenTypeContext.@default());
            _1630_boundTpe = _out166;
            readIdents = _1629_recIdents;
            Dafny.ISequence<Dafny.Rune> _1631_boundRName;
            _1631_boundRName = DCOMP.__default.escapeName(_1623_boundName);
            RAST._IExpr _1632_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1633_bodyIdents;
            DCOMP._IEnvironment _1634_bodyEnv;
            RAST._IExpr _out167;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out168;
            DCOMP._IEnvironment _out169;
            (this).GenStmts(_1626_body, selfIdent, (env).AddAssigned(_1631_boundRName, _1630_boundTpe), false, earlyReturn, out _out167, out _out168, out _out169);
            _1632_bodyExpr = _out167;
            _1633_bodyIdents = _out168;
            _1634_bodyEnv = _out169;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1633_bodyIdents), Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1631_boundRName));
            newEnv = env;
            generated = RAST.Expr.create_For(_1631_boundRName, _1627_over, _1632_bodyExpr);
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Break) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _1635_toLabel = _source74.dtor_toLabel;
          unmatched74 = false;
          {
            Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _source75 = _1635_toLabel;
            bool unmatched75 = true;
            if (unmatched75) {
              if (_source75.is_Some) {
                Dafny.ISequence<Dafny.Rune> _1636_lbl = _source75.dtor_value;
                unmatched75 = false;
                {
                  generated = RAST.Expr.create_Break(Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("label_"), _1636_lbl)));
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
          Dafny.ISequence<DAST._IStatement> _1637_body = _source74.dtor_body;
          unmatched74 = false;
          {
            generated = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            if (!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) {
              RAST._IExpr _1638_selfClone;
              DCOMP._IOwnership _1639___v87;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1640___v88;
              RAST._IExpr _out170;
              DCOMP._IOwnership _out171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out172;
              (this).GenIdent((selfIdent).dtor_rSelfName, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out170, out _out171, out _out172);
              _1638_selfClone = _out170;
              _1639___v87 = _out171;
              _1640___v88 = _out172;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1638_selfClone)));
            }
            newEnv = env;
            BigInteger _hi34 = new BigInteger(((env).dtor_names).Count);
            for (BigInteger _1641_paramI = BigInteger.Zero; _1641_paramI < _hi34; _1641_paramI++) {
              Dafny.ISequence<Dafny.Rune> _1642_param;
              _1642_param = ((env).dtor_names).Select(_1641_paramI);
              RAST._IExpr _1643_paramInit;
              DCOMP._IOwnership _1644___v89;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1645___v90;
              RAST._IExpr _out173;
              DCOMP._IOwnership _out174;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out175;
              (this).GenIdent(_1642_param, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out173, out _out174, out _out175);
              _1643_paramInit = _out173;
              _1644___v89 = _out174;
              _1645___v90 = _out175;
              generated = (generated).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _1642_param, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_1643_paramInit)));
              if (((env).dtor_types).Contains(_1642_param)) {
                RAST._IType _1646_declaredType;
                _1646_declaredType = (Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Select((env).dtor_types,_1642_param)).ToOwned();
                newEnv = (newEnv).AddAssigned(_1642_param, _1646_declaredType);
              }
            }
            RAST._IExpr _1647_bodyExpr;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1648_bodyIdents;
            DCOMP._IEnvironment _1649_bodyEnv;
            RAST._IExpr _out176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out177;
            DCOMP._IEnvironment _out178;
            (this).GenStmts(_1637_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), newEnv, false, earlyReturn, out _out176, out _out177, out _out178);
            _1647_bodyExpr = _out176;
            _1648_bodyIdents = _out177;
            _1649_bodyEnv = _out178;
            readIdents = _1648_bodyIdents;
            generated = (generated).Then(RAST.Expr.create_Labelled(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TAIL_CALL_START"), RAST.Expr.create_Loop(Std.Wrappers.Option<RAST._IExpr>.create_None(), _1647_bodyExpr)));
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
          DAST._IExpression _1650_on = _source74.dtor_on;
          DAST._ICallName _1651_name = _source74.dtor_callName;
          Dafny.ISequence<DAST._IType> _1652_typeArgs = _source74.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1653_args = _source74.dtor_args;
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> _1654_maybeOutVars = _source74.dtor_outs;
          unmatched74 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1655_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1656_recIdents;
            Dafny.ISequence<RAST._IType> _1657_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _1658_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out180;
            Dafny.ISequence<RAST._IType> _out181;
            Std.Wrappers._IOption<DAST._IResolvedType> _out182;
            (this).GenArgs(selfIdent, _1651_name, _1652_typeArgs, _1653_args, env, out _out179, out _out180, out _out181, out _out182);
            _1655_argExprs = _out179;
            _1656_recIdents = _out180;
            _1657_typeExprs = _out181;
            _1658_fullNameQualifier = _out182;
            readIdents = _1656_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source76 = _1658_fullNameQualifier;
            bool unmatched76 = true;
            if (unmatched76) {
              if (_source76.is_Some) {
                DAST._IResolvedType value9 = _source76.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1659_path = value9.dtor_path;
                Dafny.ISequence<DAST._IType> _1660_onTypeArgs = value9.dtor_typeArgs;
                DAST._IResolvedTypeBase _1661_base = value9.dtor_kind;
                Dafny.ISequence<DAST._IAttribute> _1662___v91 = value9.dtor_attributes;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1663___v92 = value9.dtor_properMethods;
                Dafny.ISequence<DAST._IType> _1664___v93 = value9.dtor_extendedTypes;
                unmatched76 = false;
                RAST._IExpr _1665_fullPath;
                RAST._IExpr _out183;
                _out183 = DCOMP.COMP.GenPathExpr(_1659_path);
                _1665_fullPath = _out183;
                Dafny.ISequence<RAST._IType> _1666_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out184;
                _out184 = (this).GenTypeArgs(_1660_onTypeArgs, DCOMP.GenTypeContext.@default());
                _1666_onTypeExprs = _out184;
                RAST._IExpr _1667_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _1668_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1669_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_1661_base).is_Trait) || ((_1661_base).is_Class)) {
                  RAST._IExpr _out185;
                  DCOMP._IOwnership _out186;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out187;
                  (this).GenExpr(_1650_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out185, out _out186, out _out187);
                  _1667_onExpr = _out185;
                  _1668_recOwnership = _out186;
                  _1669_recIdents = _out187;
                  _1667_onExpr = ((this).modify__macro).Apply1(_1667_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1669_recIdents);
                } else {
                  RAST._IExpr _out188;
                  DCOMP._IOwnership _out189;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out190;
                  (this).GenExpr(_1650_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowedMut(), out _out188, out _out189, out _out190);
                  _1667_onExpr = _out188;
                  _1668_recOwnership = _out189;
                  _1669_recIdents = _out190;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1669_recIdents);
                }
                generated = ((((_1665_fullPath).ApplyType(_1666_onTypeExprs)).MSel(DCOMP.__default.escapeName((_1651_name).dtor_name))).ApplyType(_1657_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_1667_onExpr), _1655_argExprs));
              }
            }
            if (unmatched76) {
              Std.Wrappers._IOption<DAST._IResolvedType> _1670___v94 = _source76;
              unmatched76 = false;
              RAST._IExpr _1671_onExpr;
              DCOMP._IOwnership _1672___v95;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1673_enclosingIdents;
              RAST._IExpr _out191;
              DCOMP._IOwnership _out192;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out193;
              (this).GenExpr(_1650_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out191, out _out192, out _out193);
              _1671_onExpr = _out191;
              _1672___v95 = _out192;
              _1673_enclosingIdents = _out193;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1673_enclosingIdents);
              Dafny.ISequence<Dafny.Rune> _1674_renderedName;
              _1674_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
                DAST._ICallName _source77 = _1651_name;
                bool unmatched77 = true;
                if (unmatched77) {
                  if (_source77.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _1675_name = _source77.dtor_name;
                    Std.Wrappers._IOption<DAST._IType> _1676___v96 = _source77.dtor_onType;
                    Std.Wrappers._IOption<DAST._IFormal> _1677___v97 = _source77.dtor_receiverArgs;
                    Dafny.ISequence<DAST._IFormal> _1678___v98 = _source77.dtor_signature;
                    unmatched77 = false;
                    return DCOMP.__default.escapeName(_1675_name);
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
              DAST._IExpression _source78 = _1650_on;
              bool unmatched78 = true;
              if (unmatched78) {
                if (_source78.is_Companion) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1679___v99 = _source78.dtor_Companion_a0;
                  Dafny.ISequence<DAST._IType> _1680___v100 = _source78.dtor_typeArgs;
                  unmatched78 = false;
                  {
                    _1671_onExpr = (_1671_onExpr).MSel(_1674_renderedName);
                  }
                }
              }
              if (unmatched78) {
                DAST._IExpression _1681___v101 = _source78;
                unmatched78 = false;
                {
                  if (!object.Equals(_1671_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source79 = _1651_name;
                    bool unmatched79 = true;
                    if (unmatched79) {
                      if (_source79.is_CallName) {
                        Dafny.ISequence<Dafny.Rune> _1682___v102 = _source79.dtor_name;
                        Std.Wrappers._IOption<DAST._IType> onType0 = _source79.dtor_onType;
                        if (onType0.is_Some) {
                          DAST._IType _1683_tpe = onType0.dtor_value;
                          Std.Wrappers._IOption<DAST._IFormal> _1684___v103 = _source79.dtor_receiverArgs;
                          Dafny.ISequence<DAST._IFormal> _1685___v104 = _source79.dtor_signature;
                          unmatched79 = false;
                          RAST._IType _1686_typ;
                          RAST._IType _out194;
                          _out194 = (this).GenType(_1683_tpe, DCOMP.GenTypeContext.@default());
                          _1686_typ = _out194;
                          if (((_1686_typ).IsObjectOrPointer()) && (!object.Equals(_1671_onExpr, RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))))) {
                            _1671_onExpr = ((this).modify__macro).Apply1(_1671_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched79) {
                      DAST._ICallName _1687___v105 = _source79;
                      unmatched79 = false;
                    }
                  }
                  _1671_onExpr = (_1671_onExpr).Sel(_1674_renderedName);
                }
              }
              generated = ((_1671_onExpr).ApplyType(_1657_typeExprs)).Apply(_1655_argExprs);
            }
            if (((_1654_maybeOutVars).is_Some) && ((new BigInteger(((_1654_maybeOutVars).dtor_value).Count)) == (BigInteger.One))) {
              Dafny.ISequence<Dafny.Rune> _1688_outVar;
              _1688_outVar = DCOMP.__default.escapeName((((_1654_maybeOutVars).dtor_value).Select(BigInteger.Zero)));
              if (!((env).CanReadWithoutClone(_1688_outVar))) {
                generated = RAST.__default.MaybePlacebo(generated);
              }
              generated = RAST.__default.AssignVar(_1688_outVar, generated);
            } else if (((_1654_maybeOutVars).is_None) || ((new BigInteger(((_1654_maybeOutVars).dtor_value).Count)).Sign == 0)) {
            } else {
              Dafny.ISequence<Dafny.Rune> _1689_tmpVar;
              _1689_tmpVar = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_x");
              RAST._IExpr _1690_tmpId;
              _1690_tmpId = RAST.Expr.create_Identifier(_1689_tmpVar);
              generated = RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), _1689_tmpVar, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(generated));
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1691_outVars;
              _1691_outVars = (_1654_maybeOutVars).dtor_value;
              BigInteger _hi35 = new BigInteger((_1691_outVars).Count);
              for (BigInteger _1692_outI = BigInteger.Zero; _1692_outI < _hi35; _1692_outI++) {
                Dafny.ISequence<Dafny.Rune> _1693_outVar;
                _1693_outVar = DCOMP.__default.escapeName(((_1691_outVars).Select(_1692_outI)));
                RAST._IExpr _1694_rhs;
                _1694_rhs = (_1690_tmpId).Sel(Std.Strings.__default.OfNat(_1692_outI));
                if (!((env).CanReadWithoutClone(_1693_outVar))) {
                  _1694_rhs = RAST.__default.MaybePlacebo(_1694_rhs);
                }
                generated = (generated).Then(RAST.__default.AssignVar(_1693_outVar, _1694_rhs));
              }
            }
            newEnv = env;
          }
        }
      }
      if (unmatched74) {
        if (_source74.is_Return) {
          DAST._IExpression _1695_exprDafny = _source74.dtor_expr;
          unmatched74 = false;
          {
            RAST._IExpr _1696_expr;
            DCOMP._IOwnership _1697___v106;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1698_recIdents;
            RAST._IExpr _out195;
            DCOMP._IOwnership _out196;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out197;
            (this).GenExpr(_1695_exprDafny, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out195, out _out196, out _out197);
            _1696_expr = _out195;
            _1697___v106 = _out196;
            _1698_recIdents = _out197;
            readIdents = _1698_recIdents;
            if (isLast) {
              generated = _1696_expr;
            } else {
              generated = RAST.Expr.create_Return(Std.Wrappers.Option<RAST._IExpr>.create_Some(_1696_expr));
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
        DAST._IExpression _1699_e = _source74.dtor_Print_a0;
        unmatched74 = false;
        {
          RAST._IExpr _1700_printedExpr;
          DCOMP._IOwnership _1701_recOwnership;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1702_recIdents;
          RAST._IExpr _out198;
          DCOMP._IOwnership _out199;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out200;
          (this).GenExpr(_1699_e, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out198, out _out199, out _out200);
          _1700_printedExpr = _out198;
          _1701_recOwnership = _out199;
          _1702_recIdents = _out200;
          generated = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("print!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_LiteralString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{}"), false, false), ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DafnyPrintWrapper"))).Apply1(_1700_printedExpr)));
          readIdents = _1702_recIdents;
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
        DAST._INewtypeRange _1703___v107 = _source80;
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
            bool _1704_b = _h170.dtor_BoolLiteral_a0;
            unmatched81 = false;
            {
              RAST._IExpr _out205;
              DCOMP._IOwnership _out206;
              (this).FromOwned(RAST.Expr.create_LiteralBool(_1704_b), expectedOwnership, out _out205, out _out206);
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
            Dafny.ISequence<Dafny.Rune> _1705_i = _h171.dtor_IntLiteral_a0;
            DAST._IType _1706_t = _h171.dtor_IntLiteral_a1;
            unmatched81 = false;
            {
              DAST._IType _source82 = _1706_t;
              bool unmatched82 = true;
              if (unmatched82) {
                if (_source82.is_Primitive) {
                  DAST._IPrimitive _h70 = _source82.dtor_Primitive_a0;
                  if (_h70.is_Int) {
                    unmatched82 = false;
                    {
                      if ((new BigInteger((_1705_i).Count)) <= (new BigInteger(4))) {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralInt(_1705_i));
                      } else {
                        r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(RAST.Expr.create_LiteralString(_1705_i, true, false));
                      }
                    }
                  }
                }
              }
              if (unmatched82) {
                DAST._IType _1707_o = _source82;
                unmatched82 = false;
                {
                  RAST._IType _1708_genType;
                  RAST._IType _out207;
                  _out207 = (this).GenType(_1707_o, DCOMP.GenTypeContext.@default());
                  _1708_genType = _out207;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(_1705_i), _1708_genType);
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
            Dafny.ISequence<Dafny.Rune> _1709_n = _h172.dtor_DecLiteral_a0;
            Dafny.ISequence<Dafny.Rune> _1710_d = _h172.dtor_DecLiteral_a1;
            DAST._IType _1711_t = _h172.dtor_DecLiteral_a2;
            unmatched81 = false;
            {
              DAST._IType _source83 = _1711_t;
              bool unmatched83 = true;
              if (unmatched83) {
                if (_source83.is_Primitive) {
                  DAST._IPrimitive _h71 = _source83.dtor_Primitive_a0;
                  if (_h71.is_Real) {
                    unmatched83 = false;
                    {
                      r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\""), _1709_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"")), _1710_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\", 10).unwrap())"))));
                    }
                  }
                }
              }
              if (unmatched83) {
                DAST._IType _1712_o = _source83;
                unmatched83 = false;
                {
                  RAST._IType _1713_genType;
                  RAST._IType _out210;
                  _out210 = (this).GenType(_1712_o, DCOMP.GenTypeContext.@default());
                  _1713_genType = _out210;
                  r = RAST.Expr.create_TypeAscription(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("("), _1709_n), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0 / ")), _1710_d), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".0")), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))), _1713_genType);
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
            Dafny.ISequence<Dafny.Rune> _1714_l = _h173.dtor_StringLiteral_a0;
            bool _1715_verbatim = _h173.dtor_verbatim;
            unmatched81 = false;
            {
              if (_1715_verbatim) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Verbatim strings prefixed by @ not supported yet."));
              }
              r = ((RAST.__default.dafny__runtime).MSel((this).string__of)).Apply1(RAST.Expr.create_LiteralString(_1714_l, false, _1715_verbatim));
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
            BigInteger _1716_c = _h174.dtor_CharLiteralUTF16_a0;
            unmatched81 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(_1716_c));
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
            Dafny.Rune _1717_c = _h175.dtor_CharLiteral_a0;
            unmatched81 = false;
            {
              r = RAST.Expr.create_LiteralInt(Std.Strings.__default.OfNat(new BigInteger((_1717_c).Value)));
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
        DAST._IType _1718_tpe = _h176.dtor_Null_a0;
        unmatched81 = false;
        {
          RAST._IType _1719_tpeGen;
          RAST._IType _out219;
          _out219 = (this).GenType(_1718_tpe, DCOMP.GenTypeContext.@default());
          _1719_tpeGen = _out219;
          if (((this).ObjectType).is_RawPointers) {
            r = ((RAST.__default.std).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ptr"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("null"));
          } else {
            r = RAST.Expr.create_TypeAscription(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).Apply1(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("None"))), _1719_tpeGen);
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
      DAST._IBinOp _1720_op = _let_tmp_rhs53.dtor_op;
      DAST._IExpression _1721_lExpr = _let_tmp_rhs53.dtor_left;
      DAST._IExpression _1722_rExpr = _let_tmp_rhs53.dtor_right;
      DAST.Format._IBinaryOpFormat _1723_format = _let_tmp_rhs53.dtor_format2;
      bool _1724_becomesLeftCallsRight;
      _1724_becomesLeftCallsRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source84 = _1720_op;
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
          DAST._IBinOp _1725___v108 = _source84;
          unmatched84 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1726_becomesRightCallsLeft;
      _1726_becomesRightCallsLeft = ((System.Func<bool>)(() => {
        DAST._IBinOp _source85 = _1720_op;
        bool unmatched85 = true;
        if (unmatched85) {
          if (_source85.is_In) {
            unmatched85 = false;
            return true;
          }
        }
        if (unmatched85) {
          DAST._IBinOp _1727___v109 = _source85;
          unmatched85 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      bool _1728_becomesCallLeftRight;
      _1728_becomesCallLeftRight = ((System.Func<bool>)(() => {
        DAST._IBinOp _source86 = _1720_op;
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
          DAST._IBinOp _1729___v110 = _source86;
          unmatched86 = false;
          return false;
        }
        throw new System.Exception("unexpected control point");
      }))();
      DCOMP._IOwnership _1730_expectedLeftOwnership;
      _1730_expectedLeftOwnership = ((_1724_becomesLeftCallsRight) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : ((((_1726_becomesRightCallsLeft) || (_1728_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      DCOMP._IOwnership _1731_expectedRightOwnership;
      _1731_expectedRightOwnership = (((_1724_becomesLeftCallsRight) || (_1728_becomesCallLeftRight)) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (((_1726_becomesRightCallsLeft) ? (DCOMP.Ownership.create_OwnershipAutoBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()))));
      RAST._IExpr _1732_left;
      DCOMP._IOwnership _1733___v111;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1734_recIdentsL;
      RAST._IExpr _out222;
      DCOMP._IOwnership _out223;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out224;
      (this).GenExpr(_1721_lExpr, selfIdent, env, _1730_expectedLeftOwnership, out _out222, out _out223, out _out224);
      _1732_left = _out222;
      _1733___v111 = _out223;
      _1734_recIdentsL = _out224;
      RAST._IExpr _1735_right;
      DCOMP._IOwnership _1736___v112;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1737_recIdentsR;
      RAST._IExpr _out225;
      DCOMP._IOwnership _out226;
      Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out227;
      (this).GenExpr(_1722_rExpr, selfIdent, env, _1731_expectedRightOwnership, out _out225, out _out226, out _out227);
      _1735_right = _out225;
      _1736___v112 = _out226;
      _1737_recIdentsR = _out227;
      DAST._IBinOp _source87 = _1720_op;
      bool unmatched87 = true;
      if (unmatched87) {
        if (_source87.is_In) {
          unmatched87 = false;
          {
            r = ((_1735_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("contains"))).Apply1(_1732_left);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SeqProperPrefix) {
          unmatched87 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1732_left, _1735_right, _1723_format);
        }
      }
      if (unmatched87) {
        if (_source87.is_SeqPrefix) {
          unmatched87 = false;
          r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1732_left, _1735_right, _1723_format);
        }
      }
      if (unmatched87) {
        if (_source87.is_SetMerge) {
          unmatched87 = false;
          {
            r = ((_1732_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1735_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SetSubtraction) {
          unmatched87 = false;
          {
            r = ((_1732_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1735_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SetIntersection) {
          unmatched87 = false;
          {
            r = ((_1732_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1735_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Subset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1732_left, _1735_right, _1723_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_ProperSubset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1732_left, _1735_right, _1723_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_SetDisjoint) {
          unmatched87 = false;
          {
            r = ((_1732_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1735_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MapMerge) {
          unmatched87 = false;
          {
            r = ((_1732_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1735_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MapSubtraction) {
          unmatched87 = false;
          {
            r = ((_1732_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1735_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetMerge) {
          unmatched87 = false;
          {
            r = ((_1732_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("merge"))).Apply1(_1735_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetSubtraction) {
          unmatched87 = false;
          {
            r = ((_1732_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("subtract"))).Apply1(_1735_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetIntersection) {
          unmatched87 = false;
          {
            r = ((_1732_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("intersect"))).Apply1(_1735_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Submultiset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<="), _1732_left, _1735_right, _1723_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_ProperSubmultiset) {
          unmatched87 = false;
          {
            r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), _1732_left, _1735_right, _1723_format);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_MultisetDisjoint) {
          unmatched87 = false;
          {
            r = ((_1732_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("disjoint"))).Apply1(_1735_right);
          }
        }
      }
      if (unmatched87) {
        if (_source87.is_Concat) {
          unmatched87 = false;
          {
            r = ((_1732_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("concat"))).Apply1(_1735_right);
          }
        }
      }
      if (unmatched87) {
        DAST._IBinOp _1738___v113 = _source87;
        unmatched87 = false;
        {
          if ((DCOMP.COMP.OpTable).Contains(_1720_op)) {
            r = RAST.Expr.create_BinaryOp(Dafny.Map<DAST._IBinOp, Dafny.ISequence<Dafny.Rune>>.Select(DCOMP.COMP.OpTable,_1720_op), _1732_left, _1735_right, _1723_format);
          } else {
            DAST._IBinOp _source88 = _1720_op;
            bool unmatched88 = true;
            if (unmatched88) {
              if (_source88.is_Eq) {
                bool _1739_referential = _source88.dtor_referential;
                unmatched88 = false;
                {
                  if (_1739_referential) {
                    if (((this).ObjectType).is_RawPointers) {
                      (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly"));
                      r = RAST.Expr.create_RawExpr((this.error).dtor_value);
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1732_left, _1735_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  } else {
                    if (((_1722_rExpr).is_SeqValue) && ((new BigInteger(((_1722_rExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), ((((_1732_left).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else if (((_1721_lExpr).is_SeqValue) && ((new BigInteger(((_1721_lExpr).dtor_elements).Count)).Sign == 0)) {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), RAST.Expr.create_LiteralInt(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), ((((_1735_right).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("to_array"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), DAST.Format.BinaryOpFormat.create_NoFormat());
                    } else {
                      r = RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=="), _1732_left, _1735_right, DAST.Format.BinaryOpFormat.create_NoFormat());
                    }
                  }
                }
              }
            }
            if (unmatched88) {
              if (_source88.is_EuclidianDiv) {
                unmatched88 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_division"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1732_left, _1735_right));
                }
              }
            }
            if (unmatched88) {
              if (_source88.is_EuclidianMod) {
                unmatched88 = false;
                {
                  r = (RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::euclidian_modulo"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1732_left, _1735_right));
                }
              }
            }
            if (unmatched88) {
              Dafny.ISequence<Dafny.Rune> _1740_op = _source88.dtor_Passthrough_a0;
              unmatched88 = false;
              {
                r = RAST.Expr.create_BinaryOp(_1740_op, _1732_left, _1735_right, _1723_format);
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
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1734_recIdentsL, _1737_recIdentsR);
      return ;
    }
    public void GenExprConvertToNewtype(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs54 = e;
      DAST._IExpression _1741_expr = _let_tmp_rhs54.dtor_value;
      DAST._IType _1742_fromTpe = _let_tmp_rhs54.dtor_from;
      DAST._IType _1743_toTpe = _let_tmp_rhs54.dtor_typ;
      DAST._IType _let_tmp_rhs55 = _1743_toTpe;
      DAST._IResolvedType _let_tmp_rhs56 = _let_tmp_rhs55.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1744_path = _let_tmp_rhs56.dtor_path;
      Dafny.ISequence<DAST._IType> _1745_typeArgs = _let_tmp_rhs56.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs57 = _let_tmp_rhs56.dtor_kind;
      DAST._IType _1746_b = _let_tmp_rhs57.dtor_baseType;
      DAST._INewtypeRange _1747_range = _let_tmp_rhs57.dtor_range;
      bool _1748_erase = _let_tmp_rhs57.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1749___v114 = _let_tmp_rhs56.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1750___v115 = _let_tmp_rhs56.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1751___v116 = _let_tmp_rhs56.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1752_nativeToType;
      _1752_nativeToType = DCOMP.COMP.NewtypeToRustType(_1746_b, _1747_range);
      if (object.Equals(_1742_fromTpe, _1746_b)) {
        RAST._IExpr _1753_recursiveGen;
        DCOMP._IOwnership _1754_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1755_recIdents;
        RAST._IExpr _out230;
        DCOMP._IOwnership _out231;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out232;
        (this).GenExpr(_1741_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out230, out _out231, out _out232);
        _1753_recursiveGen = _out230;
        _1754_recOwned = _out231;
        _1755_recIdents = _out232;
        readIdents = _1755_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source89 = _1752_nativeToType;
        bool unmatched89 = true;
        if (unmatched89) {
          if (_source89.is_Some) {
            RAST._IType _1756_v = _source89.dtor_value;
            unmatched89 = false;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("truncate!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1753_recursiveGen, RAST.Expr.create_ExprFromType(_1756_v)));
            RAST._IExpr _out233;
            DCOMP._IOwnership _out234;
            (this).FromOwned(r, expectedOwnership, out _out233, out _out234);
            r = _out233;
            resultingOwnership = _out234;
          }
        }
        if (unmatched89) {
          unmatched89 = false;
          if (_1748_erase) {
            r = _1753_recursiveGen;
          } else {
            RAST._IType _1757_rhsType;
            RAST._IType _out235;
            _out235 = (this).GenType(_1743_toTpe, DCOMP.GenTypeContext.InBinding());
            _1757_rhsType = _out235;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat((_1757_rhsType)._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (_1753_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
          }
          RAST._IExpr _out236;
          DCOMP._IOwnership _out237;
          (this).FromOwnership(r, _1754_recOwned, expectedOwnership, out _out236, out _out237);
          r = _out236;
          resultingOwnership = _out237;
        }
      } else {
        if ((_1752_nativeToType).is_Some) {
          DAST._IType _source90 = _1742_fromTpe;
          bool unmatched90 = true;
          if (unmatched90) {
            if (_source90.is_UserDefined) {
              DAST._IResolvedType resolved1 = _source90.dtor_resolved;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1758___v117 = resolved1.dtor_path;
              Dafny.ISequence<DAST._IType> _1759___v118 = resolved1.dtor_typeArgs;
              DAST._IResolvedTypeBase kind1 = resolved1.dtor_kind;
              if (kind1.is_Newtype) {
                DAST._IType _1760_b0 = kind1.dtor_baseType;
                DAST._INewtypeRange _1761_range0 = kind1.dtor_range;
                bool _1762_erase0 = kind1.dtor_erase;
                Dafny.ISequence<DAST._IAttribute> _1763_attributes0 = resolved1.dtor_attributes;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1764___v119 = resolved1.dtor_properMethods;
                Dafny.ISequence<DAST._IType> _1765___v120 = resolved1.dtor_extendedTypes;
                unmatched90 = false;
                {
                  Std.Wrappers._IOption<RAST._IType> _1766_nativeFromType;
                  _1766_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1760_b0, _1761_range0);
                  if ((_1766_nativeFromType).is_Some) {
                    RAST._IExpr _1767_recursiveGen;
                    DCOMP._IOwnership _1768_recOwned;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1769_recIdents;
                    RAST._IExpr _out238;
                    DCOMP._IOwnership _out239;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out240;
                    (this).GenExpr(_1741_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out238, out _out239, out _out240);
                    _1767_recursiveGen = _out238;
                    _1768_recOwned = _out239;
                    _1769_recIdents = _out240;
                    RAST._IExpr _out241;
                    DCOMP._IOwnership _out242;
                    (this).FromOwnership(RAST.Expr.create_TypeAscription(_1767_recursiveGen, (_1752_nativeToType).dtor_value), _1768_recOwned, expectedOwnership, out _out241, out _out242);
                    r = _out241;
                    resultingOwnership = _out242;
                    readIdents = _1769_recIdents;
                    return ;
                  }
                }
              }
            }
          }
          if (unmatched90) {
            DAST._IType _1770___v121 = _source90;
            unmatched90 = false;
          }
          if (object.Equals(_1742_fromTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1771_recursiveGen;
            DCOMP._IOwnership _1772_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1773_recIdents;
            RAST._IExpr _out243;
            DCOMP._IOwnership _out244;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out245;
            (this).GenExpr(_1741_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out243, out _out244, out _out245);
            _1771_recursiveGen = _out243;
            _1772_recOwned = _out244;
            _1773_recIdents = _out245;
            RAST._IExpr _out246;
            DCOMP._IOwnership _out247;
            (this).FromOwnership(RAST.Expr.create_TypeAscription((_1771_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")), (_1752_nativeToType).dtor_value), _1772_recOwned, expectedOwnership, out _out246, out _out247);
            r = _out246;
            resultingOwnership = _out247;
            readIdents = _1773_recIdents;
            return ;
          }
        }
        RAST._IExpr _out248;
        DCOMP._IOwnership _out249;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out250;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1741_expr, _1742_fromTpe, _1746_b), _1746_b, _1743_toTpe), selfIdent, env, expectedOwnership, out _out248, out _out249, out _out250);
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
      DAST._IExpression _1774_expr = _let_tmp_rhs58.dtor_value;
      DAST._IType _1775_fromTpe = _let_tmp_rhs58.dtor_from;
      DAST._IType _1776_toTpe = _let_tmp_rhs58.dtor_typ;
      DAST._IType _let_tmp_rhs59 = _1775_fromTpe;
      DAST._IResolvedType _let_tmp_rhs60 = _let_tmp_rhs59.dtor_resolved;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1777___v122 = _let_tmp_rhs60.dtor_path;
      Dafny.ISequence<DAST._IType> _1778___v123 = _let_tmp_rhs60.dtor_typeArgs;
      DAST._IResolvedTypeBase _let_tmp_rhs61 = _let_tmp_rhs60.dtor_kind;
      DAST._IType _1779_b = _let_tmp_rhs61.dtor_baseType;
      DAST._INewtypeRange _1780_range = _let_tmp_rhs61.dtor_range;
      bool _1781_erase = _let_tmp_rhs61.dtor_erase;
      Dafny.ISequence<DAST._IAttribute> _1782_attributes = _let_tmp_rhs60.dtor_attributes;
      Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1783___v124 = _let_tmp_rhs60.dtor_properMethods;
      Dafny.ISequence<DAST._IType> _1784___v125 = _let_tmp_rhs60.dtor_extendedTypes;
      Std.Wrappers._IOption<RAST._IType> _1785_nativeFromType;
      _1785_nativeFromType = DCOMP.COMP.NewtypeToRustType(_1779_b, _1780_range);
      if (object.Equals(_1779_b, _1776_toTpe)) {
        RAST._IExpr _1786_recursiveGen;
        DCOMP._IOwnership _1787_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1788_recIdents;
        RAST._IExpr _out251;
        DCOMP._IOwnership _out252;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out253;
        (this).GenExpr(_1774_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out251, out _out252, out _out253);
        _1786_recursiveGen = _out251;
        _1787_recOwned = _out252;
        _1788_recIdents = _out253;
        readIdents = _1788_recIdents;
        Std.Wrappers._IOption<RAST._IType> _source91 = _1785_nativeFromType;
        bool unmatched91 = true;
        if (unmatched91) {
          if (_source91.is_Some) {
            RAST._IType _1789_v = _source91.dtor_value;
            unmatched91 = false;
            RAST._IType _1790_toTpeRust;
            RAST._IType _out254;
            _out254 = (this).GenType(_1776_toTpe, DCOMP.GenTypeContext.@default());
            _1790_toTpeRust = _out254;
            r = (((RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Into"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1790_toTpeRust))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("into"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1786_recursiveGen));
            RAST._IExpr _out255;
            DCOMP._IOwnership _out256;
            (this).FromOwned(r, expectedOwnership, out _out255, out _out256);
            r = _out255;
            resultingOwnership = _out256;
          }
        }
        if (unmatched91) {
          unmatched91 = false;
          if (_1781_erase) {
            r = _1786_recursiveGen;
          } else {
            r = (_1786_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0"));
          }
          RAST._IExpr _out257;
          DCOMP._IOwnership _out258;
          (this).FromOwnership(r, _1787_recOwned, expectedOwnership, out _out257, out _out258);
          r = _out257;
          resultingOwnership = _out258;
        }
      } else {
        if ((_1785_nativeFromType).is_Some) {
          if (object.Equals(_1776_toTpe, DAST.Type.create_Primitive(DAST.Primitive.create_Char()))) {
            RAST._IExpr _1791_recursiveGen;
            DCOMP._IOwnership _1792_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1793_recIdents;
            RAST._IExpr _out259;
            DCOMP._IOwnership _out260;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out261;
            (this).GenExpr(_1774_expr, selfIdent, env, expectedOwnership, out _out259, out _out260, out _out261);
            _1791_recursiveGen = _out259;
            _1792_recOwned = _out260;
            _1793_recIdents = _out261;
            RAST._IExpr _out262;
            DCOMP._IOwnership _out263;
            (this).FromOwnership(((RAST.__default.dafny__runtime).MSel((this).DafnyChar)).Apply1(RAST.Expr.create_TypeAscription(_1791_recursiveGen, (this).DafnyCharUnderlying)), _1792_recOwned, expectedOwnership, out _out262, out _out263);
            r = _out262;
            resultingOwnership = _out263;
            readIdents = _1793_recIdents;
            return ;
          }
        }
        RAST._IExpr _out264;
        DCOMP._IOwnership _out265;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out266;
        (this).GenExpr(DAST.Expression.create_Convert(DAST.Expression.create_Convert(_1774_expr, _1775_fromTpe, _1779_b), _1779_b, _1776_toTpe), selfIdent, env, expectedOwnership, out _out264, out _out265, out _out266);
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
        Std.Wrappers._IResult<__T, __E> _1794_valueOrError0 = (xs).Select(BigInteger.Zero);
        if ((_1794_valueOrError0).IsFailure()) {
          return (_1794_valueOrError0).PropagateFailure<Dafny.ISequence<__T>>();
        } else {
          __T _1795_head = (_1794_valueOrError0).Extract();
          Std.Wrappers._IResult<Dafny.ISequence<__T>, __E> _1796_valueOrError1 = (this).SeqResultToResultSeq<__T, __E>((xs).Drop(BigInteger.One));
          if ((_1796_valueOrError1).IsFailure()) {
            return (_1796_valueOrError1).PropagateFailure<Dafny.ISequence<__T>>();
          } else {
            Dafny.ISequence<__T> _1797_tail = (_1796_valueOrError1).Extract();
            return Std.Wrappers.Result<Dafny.ISequence<__T>, __E>.create_Success(Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(_1795_head), _1797_tail));
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
          RAST._IType _1798_fromTpeUnderlying = (fromTpe).ObjectOrPointerUnderlying();
          RAST._IType _1799_toTpeUnderlying = (toTpe).ObjectOrPointerUnderlying();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.__default.dafny__runtime).MSel((this).upcast)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1798_fromTpeUnderlying, _1799_toTpeUnderlying))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
        }
      } else if ((typeParams).Contains(_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe))) {
        return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.Select(typeParams,_System.Tuple2<RAST._IType, RAST._IType>.create(fromTpe, toTpe)));
      } else if (((fromTpe).IsRc()) && ((toTpe).IsRc())) {
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1800_valueOrError0 = (this).UpcastConversionLambda(fromType, (fromTpe).RcUnderlying(), toType, (toTpe).RcUnderlying(), typeParams);
        if ((_1800_valueOrError0).IsFailure()) {
          return (_1800_valueOrError0).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1801_lambda = (_1800_valueOrError0).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("rc_coerce"))).Apply1(_1801_lambda));
        }
      } else if ((this).SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe)) {
        Std.Wrappers._IResult<Dafny.ISequence<RAST._IExpr>, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1802_valueOrError1 = (this).SeqResultToResultSeq<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>(((System.Func<Dafny.ISequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>>) (() => {
          BigInteger dim12 = new BigInteger(((fromTpe).dtor_arguments).Count);
          var arr12 = new Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>[Dafny.Helpers.ToIntChecked(dim12, "array size exceeds memory limit")];
          for (int i12 = 0; i12 < dim12; i12++) {
            var _1803_i = (BigInteger) i12;
            arr12[(int)(_1803_i)] = (this).UpcastConversionLambda((((fromType).dtor_resolved).dtor_typeArgs).Select(_1803_i), ((fromTpe).dtor_arguments).Select(_1803_i), (((toType).dtor_resolved).dtor_typeArgs).Select(_1803_i), ((toTpe).dtor_arguments).Select(_1803_i), typeParams);
          }
          return Dafny.Sequence<Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>>.FromArray(arr12);
        }))());
        if ((_1802_valueOrError1).IsFailure()) {
          return (_1802_valueOrError1).PropagateFailure<RAST._IExpr>();
        } else {
          Dafny.ISequence<RAST._IExpr> _1804_lambdas = (_1802_valueOrError1).Extract();
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success((((RAST.Expr.create_ExprFromType((fromTpe).dtor_baseName)).ApplyType(((System.Func<Dafny.ISequence<RAST._IType>>) (() => {
  BigInteger dim13 = new BigInteger(((fromTpe).dtor_arguments).Count);
  var arr13 = new RAST._IType[Dafny.Helpers.ToIntChecked(dim13, "array size exceeds memory limit")];
  for (int i13 = 0; i13 < dim13; i13++) {
    var _1805_i = (BigInteger) i13;
    arr13[(int)(_1805_i)] = ((fromTpe).dtor_arguments).Select(_1805_i);
  }
  return Dafny.Sequence<RAST._IType>.FromArray(arr13);
}))())).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply(_1804_lambdas));
        }
      } else if (((((fromTpe).IsBuiltinCollection()) && ((toTpe).IsBuiltinCollection())) && ((this).IsBuiltinCollection(fromType))) && ((this).IsBuiltinCollection(toType))) {
        RAST._IType _1806_newFromTpe = (fromTpe).GetBuiltinCollectionElement();
        RAST._IType _1807_newToTpe = (toTpe).GetBuiltinCollectionElement();
        DAST._IType _1808_newFromType = (this).GetBuiltinCollectionElement(fromType);
        DAST._IType _1809_newToType = (this).GetBuiltinCollectionElement(toType);
        Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1810_valueOrError2 = (this).UpcastConversionLambda(_1808_newFromType, _1806_newFromTpe, _1809_newToType, _1807_newToTpe, typeParams);
        if ((_1810_valueOrError2).IsFailure()) {
          return (_1810_valueOrError2).PropagateFailure<RAST._IExpr>();
        } else {
          RAST._IExpr _1811_coerceArg = (_1810_valueOrError2).Extract();
          RAST._IExpr _1812_collectionType = (RAST.__default.dafny__runtime).MSel(((fromTpe).dtor_baseName).dtor_name);
          RAST._IExpr _1813_baseType = (((((fromTpe).dtor_baseName).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Map"))) ? ((_1812_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(((fromTpe).dtor_arguments).Select(BigInteger.Zero), _1806_newFromTpe))) : ((_1812_collectionType).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1806_newFromTpe))));
          return Std.Wrappers.Result<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>>.create_Success(((_1813_baseType).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("coerce"))).Apply1(_1811_coerceArg));
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
      DAST._IExpression _1814_expr = _let_tmp_rhs62.dtor_value;
      DAST._IType _1815_fromTpe = _let_tmp_rhs62.dtor_from;
      DAST._IType _1816_toTpe = _let_tmp_rhs62.dtor_typ;
      RAST._IType _1817_fromTpeGen;
      RAST._IType _out267;
      _out267 = (this).GenType(_1815_fromTpe, DCOMP.GenTypeContext.InBinding());
      _1817_fromTpeGen = _out267;
      RAST._IType _1818_toTpeGen;
      RAST._IType _out268;
      _out268 = (this).GenType(_1816_toTpe, DCOMP.GenTypeContext.InBinding());
      _1818_toTpeGen = _out268;
      Std.Wrappers._IResult<RAST._IExpr, _System._ITuple5<DAST._IType, RAST._IType, DAST._IType, RAST._IType, Dafny.IMap<_System._ITuple2<RAST._IType, RAST._IType>,RAST._IExpr>>> _1819_upcastConverter;
      _1819_upcastConverter = (this).UpcastConversionLambda(_1815_fromTpe, _1817_fromTpeGen, _1816_toTpe, _1818_toTpeGen, Dafny.Map<_System._ITuple2<RAST._IType, RAST._IType>, RAST._IExpr>.FromElements());
      if ((_1819_upcastConverter).is_Success) {
        RAST._IExpr _1820_conversionLambda;
        _1820_conversionLambda = (_1819_upcastConverter).dtor_value;
        RAST._IExpr _1821_recursiveGen;
        DCOMP._IOwnership _1822_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1823_recIdents;
        RAST._IExpr _out269;
        DCOMP._IOwnership _out270;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out271;
        (this).GenExpr(_1814_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out269, out _out270, out _out271);
        _1821_recursiveGen = _out269;
        _1822_recOwned = _out270;
        _1823_recIdents = _out271;
        readIdents = _1823_recIdents;
        r = (_1820_conversionLambda).Apply1(_1821_recursiveGen);
        RAST._IExpr _out272;
        DCOMP._IOwnership _out273;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out272, out _out273);
        r = _out272;
        resultingOwnership = _out273;
      } else if ((this).IsDowncastConversion(_1817_fromTpeGen, _1818_toTpeGen)) {
        RAST._IExpr _1824_recursiveGen;
        DCOMP._IOwnership _1825_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1826_recIdents;
        RAST._IExpr _out274;
        DCOMP._IOwnership _out275;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out276;
        (this).GenExpr(_1814_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out274, out _out275, out _out276);
        _1824_recursiveGen = _out274;
        _1825_recOwned = _out275;
        _1826_recIdents = _out276;
        readIdents = _1826_recIdents;
        _1818_toTpeGen = (_1818_toTpeGen).ObjectOrPointerUnderlying();
        r = ((RAST.__default.dafny__runtime).MSel((this).downcast)).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_1824_recursiveGen, RAST.Expr.create_ExprFromType(_1818_toTpeGen)));
        RAST._IExpr _out277;
        DCOMP._IOwnership _out278;
        (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out277, out _out278);
        r = _out277;
        resultingOwnership = _out278;
      } else {
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Cast coercion failed because: ")).ToVerbatimString(false));
        Dafny.Helpers.Print((_1819_upcastConverter));
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
        RAST._IExpr _1827_recursiveGen;
        DCOMP._IOwnership _1828_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1829_recIdents;
        RAST._IExpr _out279;
        DCOMP._IOwnership _out280;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out281;
        (this).GenExpr(_1814_expr, selfIdent, env, expectedOwnership, out _out279, out _out280, out _out281);
        _1827_recursiveGen = _out279;
        _1828_recOwned = _out280;
        _1829_recIdents = _out281;
        readIdents = _1829_recIdents;
        Dafny.ISequence<Dafny.Rune> _1830_msg;
        _1830_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("/* <i>Coercion from "), (_1817_fromTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" to ")), (_1818_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("</i> not yet implemented */"));
        (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1830_msg);
        r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat((_1827_recursiveGen)._ToString(DCOMP.__default.IND), _1830_msg));
        RAST._IExpr _out282;
        DCOMP._IOwnership _out283;
        (this).FromOwnership(r, _1828_recOwned, expectedOwnership, out _out282, out _out283);
        r = _out282;
        resultingOwnership = _out283;
      }
    }
    public void GenExprConvert(DAST._IExpression e, DCOMP._ISelfInfo selfIdent, DCOMP._IEnvironment env, DCOMP._IOwnership expectedOwnership, out RAST._IExpr r, out DCOMP._IOwnership resultingOwnership, out Dafny.ISet<Dafny.ISequence<Dafny.Rune>> readIdents)
    {
      r = RAST.Expr.Default();
      resultingOwnership = DCOMP.Ownership.Default();
      readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
      DAST._IExpression _let_tmp_rhs63 = e;
      DAST._IExpression _1831_expr = _let_tmp_rhs63.dtor_value;
      DAST._IType _1832_fromTpe = _let_tmp_rhs63.dtor_from;
      DAST._IType _1833_toTpe = _let_tmp_rhs63.dtor_typ;
      if (object.Equals(_1832_fromTpe, _1833_toTpe)) {
        RAST._IExpr _1834_recursiveGen;
        DCOMP._IOwnership _1835_recOwned;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1836_recIdents;
        RAST._IExpr _out284;
        DCOMP._IOwnership _out285;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out286;
        (this).GenExpr(_1831_expr, selfIdent, env, expectedOwnership, out _out284, out _out285, out _out286);
        _1834_recursiveGen = _out284;
        _1835_recOwned = _out285;
        _1836_recIdents = _out286;
        r = _1834_recursiveGen;
        RAST._IExpr _out287;
        DCOMP._IOwnership _out288;
        (this).FromOwnership(r, _1835_recOwned, expectedOwnership, out _out287, out _out288);
        r = _out287;
        resultingOwnership = _out288;
        readIdents = _1836_recIdents;
      } else {
        _System._ITuple2<DAST._IType, DAST._IType> _source92 = _System.Tuple2<DAST._IType, DAST._IType>.create(_1832_fromTpe, _1833_toTpe);
        bool unmatched92 = true;
        if (unmatched92) {
          DAST._IType _1837___v126 = _source92.dtor__0;
          DAST._IType _10 = _source92.dtor__1;
          if (_10.is_UserDefined) {
            DAST._IResolvedType resolved2 = _10.dtor_resolved;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1838___v127 = resolved2.dtor_path;
            Dafny.ISequence<DAST._IType> _1839___v128 = resolved2.dtor_typeArgs;
            DAST._IResolvedTypeBase kind2 = resolved2.dtor_kind;
            if (kind2.is_Newtype) {
              DAST._IType _1840_b = kind2.dtor_baseType;
              DAST._INewtypeRange _1841_range = kind2.dtor_range;
              bool _1842_erase = kind2.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1843_attributes = resolved2.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1844___v129 = resolved2.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1845___v130 = resolved2.dtor_extendedTypes;
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
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1846___v131 = resolved3.dtor_path;
            Dafny.ISequence<DAST._IType> _1847___v132 = resolved3.dtor_typeArgs;
            DAST._IResolvedTypeBase kind3 = resolved3.dtor_kind;
            if (kind3.is_Newtype) {
              DAST._IType _1848_b = kind3.dtor_baseType;
              DAST._INewtypeRange _1849_range = kind3.dtor_range;
              bool _1850_erase = kind3.dtor_erase;
              Dafny.ISequence<DAST._IAttribute> _1851_attributes = resolved3.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1852___v133 = resolved3.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1853___v134 = resolved3.dtor_extendedTypes;
              DAST._IType _1854___v135 = _source92.dtor__1;
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
                    RAST._IExpr _1855_recursiveGen;
                    DCOMP._IOwnership _1856___v136;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1857_recIdents;
                    RAST._IExpr _out295;
                    DCOMP._IOwnership _out296;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out297;
                    (this).GenExpr(_1831_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out295, out _out296, out _out297);
                    _1855_recursiveGen = _out295;
                    _1856___v136 = _out296;
                    _1857_recIdents = _out297;
                    r = RAST.__default.RcNew(RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::BigRational::from_integer("), (_1855_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")"))));
                    RAST._IExpr _out298;
                    DCOMP._IOwnership _out299;
                    (this).FromOwned(r, expectedOwnership, out _out298, out _out299);
                    r = _out298;
                    resultingOwnership = _out299;
                    readIdents = _1857_recIdents;
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
                    RAST._IExpr _1858_recursiveGen;
                    DCOMP._IOwnership _1859___v137;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1860_recIdents;
                    RAST._IExpr _out300;
                    DCOMP._IOwnership _out301;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out302;
                    (this).GenExpr(_1831_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out300, out _out301, out _out302);
                    _1858_recursiveGen = _out300;
                    _1859___v137 = _out301;
                    _1860_recIdents = _out302;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::dafny_rational_to_int("), (_1858_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                    RAST._IExpr _out303;
                    DCOMP._IOwnership _out304;
                    (this).FromOwned(r, expectedOwnership, out _out303, out _out304);
                    r = _out303;
                    resultingOwnership = _out304;
                    readIdents = _1860_recIdents;
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
                Dafny.ISequence<Dafny.Rune> _1861___v138 = _13.dtor_Passthrough_a0;
                unmatched92 = false;
                {
                  RAST._IType _1862_rhsType;
                  RAST._IType _out305;
                  _out305 = (this).GenType(_1833_toTpe, DCOMP.GenTypeContext.InBinding());
                  _1862_rhsType = _out305;
                  RAST._IExpr _1863_recursiveGen;
                  DCOMP._IOwnership _1864___v139;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1865_recIdents;
                  RAST._IExpr _out306;
                  DCOMP._IOwnership _out307;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out308;
                  (this).GenExpr(_1831_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out306, out _out307, out _out308);
                  _1863_recursiveGen = _out306;
                  _1864___v139 = _out307;
                  _1865_recIdents = _out308;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1862_rhsType)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1863_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap()")));
                  RAST._IExpr _out309;
                  DCOMP._IOwnership _out310;
                  (this).FromOwned(r, expectedOwnership, out _out309, out _out310);
                  r = _out309;
                  resultingOwnership = _out310;
                  readIdents = _1865_recIdents;
                }
              }
            }
          }
        }
        if (unmatched92) {
          DAST._IType _04 = _source92.dtor__0;
          if (_04.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1866___v140 = _04.dtor_Passthrough_a0;
            DAST._IType _14 = _source92.dtor__1;
            if (_14.is_Primitive) {
              DAST._IPrimitive _h77 = _14.dtor_Primitive_a0;
              if (_h77.is_Int) {
                unmatched92 = false;
                {
                  RAST._IType _1867_rhsType;
                  RAST._IType _out311;
                  _out311 = (this).GenType(_1832_fromTpe, DCOMP.GenTypeContext.InBinding());
                  _1867_rhsType = _out311;
                  RAST._IExpr _1868_recursiveGen;
                  DCOMP._IOwnership _1869___v141;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1870_recIdents;
                  RAST._IExpr _out312;
                  DCOMP._IOwnership _out313;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out314;
                  (this).GenExpr(_1831_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out312, out _out313, out _out314);
                  _1868_recursiveGen = _out312;
                  _1869___v141 = _out313;
                  _1870_recIdents = _out314;
                  r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from("), (_1868_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")))")));
                  RAST._IExpr _out315;
                  DCOMP._IOwnership _out316;
                  (this).FromOwned(r, expectedOwnership, out _out315, out _out316);
                  r = _out315;
                  resultingOwnership = _out316;
                  readIdents = _1870_recIdents;
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
                    RAST._IType _1871_rhsType;
                    RAST._IType _out317;
                    _out317 = (this).GenType(_1833_toTpe, DCOMP.GenTypeContext.InBinding());
                    _1871_rhsType = _out317;
                    RAST._IExpr _1872_recursiveGen;
                    DCOMP._IOwnership _1873___v142;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1874_recIdents;
                    RAST._IExpr _out318;
                    DCOMP._IOwnership _out319;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out320;
                    (this).GenExpr(_1831_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out318, out _out319, out _out320);
                    _1872_recursiveGen = _out318;
                    _1873___v142 = _out319;
                    _1874_recIdents = _out320;
                    r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::"), (this).DafnyChar), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("char::from_u32(<u32")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<u16")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as ::dafny_runtime::NumCast>::from(")), (_1872_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").unwrap())")), (((this).UnicodeChars) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".unwrap())")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
                    RAST._IExpr _out321;
                    DCOMP._IOwnership _out322;
                    (this).FromOwned(r, expectedOwnership, out _out321, out _out322);
                    r = _out321;
                    resultingOwnership = _out322;
                    readIdents = _1874_recIdents;
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
                    RAST._IType _1875_rhsType;
                    RAST._IType _out323;
                    _out323 = (this).GenType(_1832_fromTpe, DCOMP.GenTypeContext.InBinding());
                    _1875_rhsType = _out323;
                    RAST._IExpr _1876_recursiveGen;
                    DCOMP._IOwnership _1877___v143;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1878_recIdents;
                    RAST._IExpr _out324;
                    DCOMP._IOwnership _out325;
                    Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out326;
                    (this).GenExpr(_1831_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out324, out _out325, out _out326);
                    _1876_recursiveGen = _out324;
                    _1877___v143 = _out325;
                    _1878_recIdents = _out326;
                    r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1((_1876_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("0")));
                    RAST._IExpr _out327;
                    DCOMP._IOwnership _out328;
                    (this).FromOwned(r, expectedOwnership, out _out327, out _out328);
                    r = _out327;
                    resultingOwnership = _out328;
                    readIdents = _1878_recIdents;
                  }
                }
              }
            }
          }
        }
        if (unmatched92) {
          DAST._IType _07 = _source92.dtor__0;
          if (_07.is_Passthrough) {
            Dafny.ISequence<Dafny.Rune> _1879___v144 = _07.dtor_Passthrough_a0;
            DAST._IType _17 = _source92.dtor__1;
            if (_17.is_Passthrough) {
              Dafny.ISequence<Dafny.Rune> _1880___v145 = _17.dtor_Passthrough_a0;
              unmatched92 = false;
              {
                RAST._IExpr _1881_recursiveGen;
                DCOMP._IOwnership _1882___v146;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1883_recIdents;
                RAST._IExpr _out329;
                DCOMP._IOwnership _out330;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out331;
                (this).GenExpr(_1831_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out329, out _out330, out _out331);
                _1881_recursiveGen = _out329;
                _1882___v146 = _out330;
                _1883_recIdents = _out331;
                RAST._IType _1884_toTpeGen;
                RAST._IType _out332;
                _out332 = (this).GenType(_1833_toTpe, DCOMP.GenTypeContext.InBinding());
                _1884_toTpeGen = _out332;
                r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(("), (_1881_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ")), (_1884_toTpeGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")));
                RAST._IExpr _out333;
                DCOMP._IOwnership _out334;
                (this).FromOwned(r, expectedOwnership, out _out333, out _out334);
                r = _out333;
                resultingOwnership = _out334;
                readIdents = _1883_recIdents;
              }
            }
          }
        }
        if (unmatched92) {
          _System._ITuple2<DAST._IType, DAST._IType> _1885___v147 = _source92;
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
      Std.Wrappers._IOption<RAST._IType> _1886_tpe;
      _1886_tpe = (env).GetType(rName);
      Std.Wrappers._IOption<RAST._IType> _1887_placeboOpt;
      _1887_placeboOpt = (((_1886_tpe).is_Some) ? (((_1886_tpe).dtor_value).ExtractMaybePlacebo()) : (Std.Wrappers.Option<RAST._IType>.create_None()));
      bool _1888_currentlyBorrowed;
      _1888_currentlyBorrowed = (env).IsBorrowed(rName);
      bool _1889_noNeedOfClone;
      _1889_noNeedOfClone = (env).CanReadWithoutClone(rName);
      if ((_1887_placeboOpt).is_Some) {
        r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("read"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
        _1888_currentlyBorrowed = false;
        _1889_noNeedOfClone = true;
        _1886_tpe = Std.Wrappers.Option<RAST._IType>.create_Some((_1887_placeboOpt).dtor_value);
      }
      if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipAutoBorrowed())) {
        resultingOwnership = ((_1888_currentlyBorrowed) ? (DCOMP.Ownership.create_OwnershipBorrowed()) : (DCOMP.Ownership.create_OwnershipOwned()));
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipBorrowedMut())) {
        if ((rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
        } else {
          if (((_1886_tpe).is_Some) && (((_1886_tpe).dtor_value).IsObjectOrPointer())) {
            r = ((this).modify__macro).Apply1(r);
          } else {
            r = RAST.__default.BorrowMut(r);
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowedMut();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwned())) {
        bool _1890_needObjectFromRef;
        _1890_needObjectFromRef = ((((selfIdent).is_ThisTyped) && ((selfIdent).IsSelf())) && (((selfIdent).dtor_rSelfName).Equals(rName))) && (((System.Func<bool>)(() => {
          DAST._IType _source93 = (selfIdent).dtor_dafnyType;
          bool unmatched93 = true;
          if (unmatched93) {
            if (_source93.is_UserDefined) {
              DAST._IResolvedType resolved4 = _source93.dtor_resolved;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1891___v148 = resolved4.dtor_path;
              Dafny.ISequence<DAST._IType> _1892___v149 = resolved4.dtor_typeArgs;
              DAST._IResolvedTypeBase _1893_base = resolved4.dtor_kind;
              Dafny.ISequence<DAST._IAttribute> _1894_attributes = resolved4.dtor_attributes;
              Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1895___v150 = resolved4.dtor_properMethods;
              Dafny.ISequence<DAST._IType> _1896___v151 = resolved4.dtor_extendedTypes;
              unmatched93 = false;
              return ((_1893_base).is_Class) || ((_1893_base).is_Trait);
            }
          }
          if (unmatched93) {
            DAST._IType _1897___v152 = _source93;
            unmatched93 = false;
            return false;
          }
          throw new System.Exception("unexpected control point");
        }))());
        if (_1890_needObjectFromRef) {
          r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Object"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(RAST.__default.RawType(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"))))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(r));
        } else {
          if (!(_1889_noNeedOfClone)) {
            r = (r).Clone();
          }
        }
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwned();
      } else if (object.Equals(expectedOwnership, DCOMP.Ownership.create_OwnershipOwnedBox())) {
        if (!(_1889_noNeedOfClone)) {
          r = (r).Clone();
        }
        r = RAST.__default.BoxNew(r);
        resultingOwnership = DCOMP.Ownership.create_OwnershipOwnedBox();
      } else if (_1888_currentlyBorrowed) {
        resultingOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
      } else {
        if (!(rName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"))) {
          if (((_1886_tpe).is_Some) && (((_1886_tpe).dtor_value).IsPointer())) {
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
      return Dafny.Helpers.Id<Func<Dafny.ISequence<DAST._IAttribute>, bool>>((_1898_attributes) => Dafny.Helpers.Quantifier<DAST._IAttribute>((_1898_attributes).UniqueElements, false, (((_exists_var_1) => {
        DAST._IAttribute _1899_attribute = (DAST._IAttribute)_exists_var_1;
        return ((_1898_attributes).Contains(_1899_attribute)) && ((((_1899_attribute).dtor_name).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("extern"))) && ((new BigInteger(((_1899_attribute).dtor_args).Count)) == (new BigInteger(2))));
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
      for (BigInteger _1900_i = BigInteger.Zero; _1900_i < _hi36; _1900_i++) {
        DCOMP._IOwnership _1901_argOwnership;
        _1901_argOwnership = DCOMP.Ownership.create_OwnershipBorrowed();
        if (((name).is_CallName) && ((_1900_i) < (new BigInteger((((name).dtor_signature)).Count)))) {
          RAST._IType _1902_tpe;
          RAST._IType _out338;
          _out338 = (this).GenType(((((name).dtor_signature)).Select(_1900_i)).dtor_typ, DCOMP.GenTypeContext.@default());
          _1902_tpe = _out338;
          if ((_1902_tpe).CanReadWithoutClone()) {
            _1901_argOwnership = DCOMP.Ownership.create_OwnershipOwned();
          }
        }
        RAST._IExpr _1903_argExpr;
        DCOMP._IOwnership _1904___v153;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1905_argIdents;
        RAST._IExpr _out339;
        DCOMP._IOwnership _out340;
        Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out341;
        (this).GenExpr((args).Select(_1900_i), selfIdent, env, _1901_argOwnership, out _out339, out _out340, out _out341);
        _1903_argExpr = _out339;
        _1904___v153 = _out340;
        _1905_argIdents = _out341;
        argExprs = Dafny.Sequence<RAST._IExpr>.Concat(argExprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1903_argExpr));
        readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1905_argIdents);
      }
      typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
      BigInteger _hi37 = new BigInteger((typeArgs).Count);
      for (BigInteger _1906_typeI = BigInteger.Zero; _1906_typeI < _hi37; _1906_typeI++) {
        RAST._IType _1907_typeExpr;
        RAST._IType _out342;
        _out342 = (this).GenType((typeArgs).Select(_1906_typeI), DCOMP.GenTypeContext.@default());
        _1907_typeExpr = _out342;
        typeExprs = Dafny.Sequence<RAST._IType>.Concat(typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1907_typeExpr));
      }
      fullNameQualifier = ((System.Func<Std.Wrappers._IOption<DAST._IResolvedType>>)(() => {
        DAST._ICallName _source94 = name;
        bool unmatched94 = true;
        if (unmatched94) {
          if (_source94.is_CallName) {
            Dafny.ISequence<Dafny.Rune> _1908_nameIdent = _source94.dtor_name;
            Std.Wrappers._IOption<DAST._IType> onType1 = _source94.dtor_onType;
            if (onType1.is_Some) {
              DAST._IType value10 = onType1.dtor_value;
              if (value10.is_UserDefined) {
                DAST._IResolvedType _1909_resolvedType = value10.dtor_resolved;
                Std.Wrappers._IOption<DAST._IFormal> _1910___v154 = _source94.dtor_receiverArgs;
                Dafny.ISequence<DAST._IFormal> _1911___v155 = _source94.dtor_signature;
                unmatched94 = false;
                if ((((_1909_resolvedType).dtor_kind).is_Trait) || (Dafny.Helpers.Id<Func<DAST._IResolvedType, Dafny.ISequence<Dafny.Rune>, bool>>((_1912_resolvedType, _1913_nameIdent) => Dafny.Helpers.Quantifier<Dafny.ISequence<Dafny.Rune>>(((_1912_resolvedType).dtor_properMethods).UniqueElements, true, (((_forall_var_8) => {
                  Dafny.ISequence<Dafny.Rune> _1914_m = (Dafny.ISequence<Dafny.Rune>)_forall_var_8;
                  return !(((_1912_resolvedType).dtor_properMethods).Contains(_1914_m)) || (!object.Equals((_1914_m), _1913_nameIdent));
                }))))(_1909_resolvedType, _1908_nameIdent))) {
                  return Std.Wrappers.Option<DAST._IResolvedType>.create_Some(Std.Wrappers.Option<DAST._IResolvedType>.GetOr(DCOMP.__default.TraitTypeContainingMethod(_1909_resolvedType, (_1908_nameIdent)), _1909_resolvedType));
                } else {
                  return Std.Wrappers.Option<DAST._IResolvedType>.create_None();
                }
              }
            }
          }
        }
        if (unmatched94) {
          DAST._ICallName _1915___v156 = _source94;
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
          DAST._ILiteral _1916___v157 = _source95.dtor_Literal_a0;
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
          Dafny.ISequence<Dafny.Rune> _1917_name = _source95.dtor_Ident_a0;
          unmatched95 = false;
          {
            RAST._IExpr _out346;
            DCOMP._IOwnership _out347;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out348;
            (this).GenIdent(DCOMP.__default.escapeName(_1917_name), selfIdent, env, expectedOwnership, out _out346, out _out347, out _out348);
            r = _out346;
            resultingOwnership = _out347;
            readIdents = _out348;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Companion) {
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1918_path = _source95.dtor_Companion_a0;
          Dafny.ISequence<DAST._IType> _1919_typeArgs = _source95.dtor_typeArgs;
          unmatched95 = false;
          {
            RAST._IExpr _out349;
            _out349 = DCOMP.COMP.GenPathExpr(_1918_path);
            r = _out349;
            if ((new BigInteger((_1919_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1920_typeExprs;
              _1920_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi38 = new BigInteger((_1919_typeArgs).Count);
              for (BigInteger _1921_i = BigInteger.Zero; _1921_i < _hi38; _1921_i++) {
                RAST._IType _1922_typeExpr;
                RAST._IType _out350;
                _out350 = (this).GenType((_1919_typeArgs).Select(_1921_i), DCOMP.GenTypeContext.@default());
                _1922_typeExpr = _out350;
                _1920_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1920_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1922_typeExpr));
              }
              r = (r).ApplyType(_1920_typeExprs);
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
          DAST._IType _1923_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            RAST._IType _1924_typExpr;
            RAST._IType _out353;
            _out353 = (this).GenType(_1923_typ, DCOMP.GenTypeContext.@default());
            _1924_typExpr = _out353;
            if ((_1924_typExpr).IsObjectOrPointer()) {
              r = (_1924_typExpr).ToNullExpr();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("<"), (_1924_typExpr)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" as std::default::Default>::default()")));
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
          Dafny.ISequence<DAST._IExpression> _1925_values = _source95.dtor_Tuple_a0;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _1926_exprs;
            _1926_exprs = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi39 = new BigInteger((_1925_values).Count);
            for (BigInteger _1927_i = BigInteger.Zero; _1927_i < _hi39; _1927_i++) {
              RAST._IExpr _1928_recursiveGen;
              DCOMP._IOwnership _1929___v158;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1930_recIdents;
              RAST._IExpr _out356;
              DCOMP._IOwnership _out357;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out358;
              (this).GenExpr((_1925_values).Select(_1927_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out356, out _out357, out _out358);
              _1928_recursiveGen = _out356;
              _1929___v158 = _out357;
              _1930_recIdents = _out358;
              _1926_exprs = Dafny.Sequence<RAST._IExpr>.Concat(_1926_exprs, Dafny.Sequence<RAST._IExpr>.FromElements(_1928_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1930_recIdents);
            }
            r = (((new BigInteger((_1925_values).Count)) <= (RAST.__default.MAX__TUPLE__SIZE)) ? (RAST.Expr.create_Tuple(_1926_exprs)) : (RAST.__default.SystemTuple(_1926_exprs)));
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
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _1931_path = _source95.dtor_path;
          Dafny.ISequence<DAST._IType> _1932_typeArgs = _source95.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _1933_args = _source95.dtor_args;
          unmatched95 = false;
          {
            RAST._IExpr _out361;
            _out361 = DCOMP.COMP.GenPathExpr(_1931_path);
            r = _out361;
            if ((new BigInteger((_1932_typeArgs).Count)).Sign == 1) {
              Dafny.ISequence<RAST._IType> _1934_typeExprs;
              _1934_typeExprs = Dafny.Sequence<RAST._IType>.FromElements();
              BigInteger _hi40 = new BigInteger((_1932_typeArgs).Count);
              for (BigInteger _1935_i = BigInteger.Zero; _1935_i < _hi40; _1935_i++) {
                RAST._IType _1936_typeExpr;
                RAST._IType _out362;
                _out362 = (this).GenType((_1932_typeArgs).Select(_1935_i), DCOMP.GenTypeContext.@default());
                _1936_typeExpr = _out362;
                _1934_typeExprs = Dafny.Sequence<RAST._IType>.Concat(_1934_typeExprs, Dafny.Sequence<RAST._IType>.FromElements(_1936_typeExpr));
              }
              r = (r).ApplyType(_1934_typeExprs);
            }
            r = (r).MSel((this).allocate__fn);
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IExpr> _1937_arguments;
            _1937_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi41 = new BigInteger((_1933_args).Count);
            for (BigInteger _1938_i = BigInteger.Zero; _1938_i < _hi41; _1938_i++) {
              RAST._IExpr _1939_recursiveGen;
              DCOMP._IOwnership _1940___v159;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1941_recIdents;
              RAST._IExpr _out363;
              DCOMP._IOwnership _out364;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out365;
              (this).GenExpr((_1933_args).Select(_1938_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out363, out _out364, out _out365);
              _1939_recursiveGen = _out363;
              _1940___v159 = _out364;
              _1941_recIdents = _out365;
              _1937_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_1937_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_1939_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1941_recIdents);
            }
            r = (r).Apply(_1937_arguments);
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
          Dafny.ISequence<DAST._IExpression> _1942_dims = _source95.dtor_dims;
          DAST._IType _1943_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            if ((new BigInteger(16)) < (new BigInteger((_1942_dims).Count))) {
              Dafny.ISequence<Dafny.Rune> _1944_msg;
              _1944_msg = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Unsupported: Creation of arrays of more than 16 dimensions");
              if ((this.error).is_None) {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_1944_msg);
              }
              r = RAST.Expr.create_RawExpr(_1944_msg);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            } else {
              r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
              RAST._IType _1945_typeGen;
              RAST._IType _out368;
              _out368 = (this).GenType(_1943_typ, DCOMP.GenTypeContext.@default());
              _1945_typeGen = _out368;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
              Dafny.ISequence<RAST._IExpr> _1946_dimExprs;
              _1946_dimExprs = Dafny.Sequence<RAST._IExpr>.FromElements();
              BigInteger _hi42 = new BigInteger((_1942_dims).Count);
              for (BigInteger _1947_i = BigInteger.Zero; _1947_i < _hi42; _1947_i++) {
                RAST._IExpr _1948_recursiveGen;
                DCOMP._IOwnership _1949___v160;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1950_recIdents;
                RAST._IExpr _out369;
                DCOMP._IOwnership _out370;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out371;
                (this).GenExpr((_1942_dims).Select(_1947_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out369, out _out370, out _out371);
                _1948_recursiveGen = _out369;
                _1949___v160 = _out370;
                _1950_recIdents = _out371;
                _1946_dimExprs = Dafny.Sequence<RAST._IExpr>.Concat(_1946_dimExprs, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_TypeAscription(_1948_recursiveGen, RAST.Type.create_TIdentifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("usize")))));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1950_recIdents);
              }
              if ((new BigInteger((_1942_dims).Count)) > (BigInteger.One)) {
                Dafny.ISequence<Dafny.Rune> _1951_class__name;
                _1951_class__name = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array"), Std.Strings.__default.OfNat(new BigInteger((_1942_dims).Count)));
                r = ((((RAST.__default.dafny__runtime).MSel(_1951_class__name)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1945_typeGen))).MSel((this).placebos__usize)).Apply(_1946_dimExprs);
              } else {
                r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).placebos__usize)).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_1945_typeGen))).Apply(_1946_dimExprs);
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
          DAST._IExpression _1952_underlying = _source95.dtor_value;
          unmatched95 = false;
          {
            RAST._IExpr _1953_recursiveGen;
            DCOMP._IOwnership _1954___v161;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1955_recIdents;
            RAST._IExpr _out374;
            DCOMP._IOwnership _out375;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out376;
            (this).GenExpr(_1952_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out374, out _out375, out _out376);
            _1953_recursiveGen = _out374;
            _1954___v161 = _out375;
            _1955_recIdents = _out376;
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(_1953_recursiveGen);
            readIdents = _1955_recIdents;
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
          DAST._IExpression _1956_underlying = _source95.dtor_value;
          DAST._IType _1957_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            RAST._IType _1958_tpe;
            RAST._IType _out379;
            _out379 = (this).GenType(_1957_typ, DCOMP.GenTypeContext.@default());
            _1958_tpe = _out379;
            RAST._IExpr _1959_recursiveGen;
            DCOMP._IOwnership _1960___v162;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1961_recIdents;
            RAST._IExpr _out380;
            DCOMP._IOwnership _out381;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out382;
            (this).GenExpr(_1956_underlying, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out380, out _out381, out _out382);
            _1959_recursiveGen = _out380;
            _1960___v162 = _out381;
            _1961_recIdents = _out382;
            readIdents = _1961_recIdents;
            if ((_1958_tpe).IsObjectOrPointer()) {
              RAST._IType _1962_t;
              _1962_t = (_1958_tpe).ObjectOrPointerUnderlying();
              if ((_1962_t).is_Array) {
                r = (((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("array"))).MSel((this).array__construct)).Apply1(_1959_recursiveGen);
              } else if ((_1962_t).IsMultiArray()) {
                Dafny.ISequence<Dafny.Rune> _1963_c;
                _1963_c = (_1962_t).MultiArrayClass();
                r = (((RAST.__default.dafny__runtime).MSel(_1963_c)).MSel((this).array__construct)).Apply1(_1959_recursiveGen);
              } else {
                (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a pointer or object type to something that is not an array or a multi array: "), (_1958_tpe)._ToString(DCOMP.__default.IND)));
                r = RAST.Expr.create_RawExpr((this.error).dtor_value);
              }
            } else {
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Finalize New Array with a type that is not a pointer or an object: "), (_1958_tpe)._ToString(DCOMP.__default.IND)));
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
          DAST._IResolvedType _1964_datatypeType = _source95.dtor_datatypeType;
          Dafny.ISequence<DAST._IType> _1965_typeArgs = _source95.dtor_typeArgs;
          Dafny.ISequence<Dafny.Rune> _1966_variant = _source95.dtor_variant;
          bool _1967_isCo = _source95.dtor_isCo;
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression>> _1968_values = _source95.dtor_contents;
          unmatched95 = false;
          {
            RAST._IExpr _out385;
            _out385 = DCOMP.COMP.GenPathExpr((_1964_datatypeType).dtor_path);
            r = _out385;
            Dafny.ISequence<RAST._IType> _1969_genTypeArgs;
            _1969_genTypeArgs = Dafny.Sequence<RAST._IType>.FromElements();
            BigInteger _hi43 = new BigInteger((_1965_typeArgs).Count);
            for (BigInteger _1970_i = BigInteger.Zero; _1970_i < _hi43; _1970_i++) {
              RAST._IType _1971_typeExpr;
              RAST._IType _out386;
              _out386 = (this).GenType((_1965_typeArgs).Select(_1970_i), DCOMP.GenTypeContext.@default());
              _1971_typeExpr = _out386;
              _1969_genTypeArgs = Dafny.Sequence<RAST._IType>.Concat(_1969_genTypeArgs, Dafny.Sequence<RAST._IType>.FromElements(_1971_typeExpr));
            }
            if ((new BigInteger((_1965_typeArgs).Count)).Sign == 1) {
              r = (r).ApplyType(_1969_genTypeArgs);
            }
            r = (r).MSel(DCOMP.__default.escapeName(_1966_variant));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IAssignIdentifier> _1972_assignments;
            _1972_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.FromElements();
            BigInteger _hi44 = new BigInteger((_1968_values).Count);
            for (BigInteger _1973_i = BigInteger.Zero; _1973_i < _hi44; _1973_i++) {
              _System._ITuple2<Dafny.ISequence<Dafny.Rune>, DAST._IExpression> _let_tmp_rhs64 = (_1968_values).Select(_1973_i);
              Dafny.ISequence<Dafny.Rune> _1974_name = _let_tmp_rhs64.dtor__0;
              DAST._IExpression _1975_value = _let_tmp_rhs64.dtor__1;
              if (_1967_isCo) {
                RAST._IExpr _1976_recursiveGen;
                DCOMP._IOwnership _1977___v163;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1978_recIdents;
                RAST._IExpr _out387;
                DCOMP._IOwnership _out388;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out389;
                (this).GenExpr(_1975_value, selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out387, out _out388, out _out389);
                _1976_recursiveGen = _out387;
                _1977___v163 = _out388;
                _1978_recIdents = _out389;
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1978_recIdents);
                Dafny.ISequence<Dafny.Rune> _1979_allReadCloned;
                _1979_allReadCloned = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
                while (!(_1978_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
                  Dafny.ISequence<Dafny.Rune> _1980_next;
                  foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_2 in (_1978_recIdents).Elements) {
                    _1980_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_2;
                    if ((_1978_recIdents).Contains(_1980_next)) {
                      goto after__ASSIGN_SUCH_THAT_2;
                    }
                  }
                  throw new System.Exception("assign-such-that search produced no value (line 4305)");
                after__ASSIGN_SUCH_THAT_2: ;
                  _1979_allReadCloned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_1979_allReadCloned, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let ")), _1980_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(" = ")), _1980_next), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(".clone();\n"));
                  _1978_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_1978_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_1980_next));
                }
                Dafny.ISequence<Dafny.Rune> _1981_wasAssigned;
                _1981_wasAssigned = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n"), _1979_allReadCloned), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move || (")), (_1976_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")})))"));
                _1972_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1972_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1974_name), RAST.Expr.create_RawExpr(_1981_wasAssigned))));
              } else {
                RAST._IExpr _1982_recursiveGen;
                DCOMP._IOwnership _1983___v164;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1984_recIdents;
                RAST._IExpr _out390;
                DCOMP._IOwnership _out391;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out392;
                (this).GenExpr(_1975_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out390, out _out391, out _out392);
                _1982_recursiveGen = _out390;
                _1983___v164 = _out391;
                _1984_recIdents = _out392;
                _1972_assignments = Dafny.Sequence<RAST._IAssignIdentifier>.Concat(_1972_assignments, Dafny.Sequence<RAST._IAssignIdentifier>.FromElements(RAST.AssignIdentifier.create(DCOMP.__default.escapeIdent(_1974_name), _1982_recursiveGen)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _1984_recIdents);
              }
            }
            r = RAST.Expr.create_StructBuild(r, _1972_assignments);
            if ((this).IsRcWrapped((_1964_datatypeType).dtor_attributes)) {
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
          DAST._IExpression _1985___v165 = _source95.dtor_value;
          DAST._IType _1986___v166 = _source95.dtor_from;
          DAST._IType _1987___v167 = _source95.dtor_typ;
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
          DAST._IExpression _1988_length = _source95.dtor_length;
          DAST._IExpression _1989_expr = _source95.dtor_elem;
          unmatched95 = false;
          {
            RAST._IExpr _1990_recursiveGen;
            DCOMP._IOwnership _1991___v168;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1992_recIdents;
            RAST._IExpr _out398;
            DCOMP._IOwnership _out399;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out400;
            (this).GenExpr(_1989_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out398, out _out399, out _out400);
            _1990_recursiveGen = _out398;
            _1991___v168 = _out399;
            _1992_recIdents = _out400;
            RAST._IExpr _1993_lengthGen;
            DCOMP._IOwnership _1994___v169;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _1995_lengthIdents;
            RAST._IExpr _out401;
            DCOMP._IOwnership _out402;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out403;
            (this).GenExpr(_1988_length, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out401, out _out402, out _out403);
            _1993_lengthGen = _out401;
            _1994___v169 = _out402;
            _1995_lengthIdents = _out403;
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\nlet _initializer = "), (_1990_recursiveGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), ")), (_1993_lengthGen)._ToString(DCOMP.__default.IND)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}")));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_1992_recIdents, _1995_lengthIdents);
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
          Dafny.ISequence<DAST._IExpression> _1996_exprs = _source95.dtor_elements;
          DAST._IType _1997_typ = _source95.dtor_typ;
          unmatched95 = false;
          {
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            RAST._IType _1998_genTpe;
            RAST._IType _out406;
            _out406 = (this).GenType(_1997_typ, DCOMP.GenTypeContext.@default());
            _1998_genTpe = _out406;
            BigInteger _1999_i;
            _1999_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2000_args;
            _2000_args = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_1999_i) < (new BigInteger((_1996_exprs).Count))) {
              RAST._IExpr _2001_recursiveGen;
              DCOMP._IOwnership _2002___v170;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2003_recIdents;
              RAST._IExpr _out407;
              DCOMP._IOwnership _out408;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out409;
              (this).GenExpr((_1996_exprs).Select(_1999_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out407, out _out408, out _out409);
              _2001_recursiveGen = _out407;
              _2002___v170 = _out408;
              _2003_recIdents = _out409;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2003_recIdents);
              _2000_args = Dafny.Sequence<RAST._IExpr>.Concat(_2000_args, Dafny.Sequence<RAST._IExpr>.FromElements(_2001_recursiveGen));
              _1999_i = (_1999_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("seq!"))).Apply(_2000_args);
            if ((new BigInteger((_2000_args).Count)).Sign == 0) {
              r = RAST.Expr.create_TypeAscription(r, ((RAST.__default.dafny__runtime__type).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Sequence"))).Apply1(_1998_genTpe));
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
          Dafny.ISequence<DAST._IExpression> _2004_exprs = _source95.dtor_elements;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2005_generatedValues;
            _2005_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2006_i;
            _2006_i = BigInteger.Zero;
            while ((_2006_i) < (new BigInteger((_2004_exprs).Count))) {
              RAST._IExpr _2007_recursiveGen;
              DCOMP._IOwnership _2008___v171;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2009_recIdents;
              RAST._IExpr _out412;
              DCOMP._IOwnership _out413;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out414;
              (this).GenExpr((_2004_exprs).Select(_2006_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out412, out _out413, out _out414);
              _2007_recursiveGen = _out412;
              _2008___v171 = _out413;
              _2009_recIdents = _out414;
              _2005_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2005_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2007_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2009_recIdents);
              _2006_i = (_2006_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("set!"))).Apply(_2005_generatedValues);
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
          Dafny.ISequence<DAST._IExpression> _2010_exprs = _source95.dtor_elements;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2011_generatedValues;
            _2011_generatedValues = Dafny.Sequence<RAST._IExpr>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2012_i;
            _2012_i = BigInteger.Zero;
            while ((_2012_i) < (new BigInteger((_2010_exprs).Count))) {
              RAST._IExpr _2013_recursiveGen;
              DCOMP._IOwnership _2014___v172;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2015_recIdents;
              RAST._IExpr _out417;
              DCOMP._IOwnership _out418;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out419;
              (this).GenExpr((_2010_exprs).Select(_2012_i), selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out417, out _out418, out _out419);
              _2013_recursiveGen = _out417;
              _2014___v172 = _out418;
              _2015_recIdents = _out419;
              _2011_generatedValues = Dafny.Sequence<RAST._IExpr>.Concat(_2011_generatedValues, Dafny.Sequence<RAST._IExpr>.FromElements(_2013_recursiveGen));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2015_recIdents);
              _2012_i = (_2012_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("multiset!"))).Apply(_2011_generatedValues);
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
          DAST._IExpression _2016_expr = _source95.dtor_ToMultiset_a0;
          unmatched95 = false;
          {
            RAST._IExpr _2017_recursiveGen;
            DCOMP._IOwnership _2018___v173;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2019_recIdents;
            RAST._IExpr _out422;
            DCOMP._IOwnership _out423;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out424;
            (this).GenExpr(_2016_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out422, out _out423, out _out424);
            _2017_recursiveGen = _out422;
            _2018___v173 = _out423;
            _2019_recIdents = _out424;
            r = ((_2017_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_dafny_multiset"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2019_recIdents;
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
          Dafny.ISequence<_System._ITuple2<DAST._IExpression, DAST._IExpression>> _2020_mapElems = _source95.dtor_mapElems;
          unmatched95 = false;
          {
            Dafny.ISequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>> _2021_generatedValues;
            _2021_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements();
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _2022_i;
            _2022_i = BigInteger.Zero;
            while ((_2022_i) < (new BigInteger((_2020_mapElems).Count))) {
              RAST._IExpr _2023_recursiveGenKey;
              DCOMP._IOwnership _2024___v174;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2025_recIdentsKey;
              RAST._IExpr _out427;
              DCOMP._IOwnership _out428;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out429;
              (this).GenExpr(((_2020_mapElems).Select(_2022_i)).dtor__0, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out427, out _out428, out _out429);
              _2023_recursiveGenKey = _out427;
              _2024___v174 = _out428;
              _2025_recIdentsKey = _out429;
              RAST._IExpr _2026_recursiveGenValue;
              DCOMP._IOwnership _2027___v175;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2028_recIdentsValue;
              RAST._IExpr _out430;
              DCOMP._IOwnership _out431;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out432;
              (this).GenExpr(((_2020_mapElems).Select(_2022_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out430, out _out431, out _out432);
              _2026_recursiveGenValue = _out430;
              _2027___v175 = _out431;
              _2028_recIdentsValue = _out432;
              _2021_generatedValues = Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.Concat(_2021_generatedValues, Dafny.Sequence<_System._ITuple2<RAST._IExpr, RAST._IExpr>>.FromElements(_System.Tuple2<RAST._IExpr, RAST._IExpr>.create(_2023_recursiveGenKey, _2026_recursiveGenValue)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2025_recIdentsKey), _2028_recIdentsValue);
              _2022_i = (_2022_i) + (BigInteger.One);
            }
            _2022_i = BigInteger.Zero;
            Dafny.ISequence<RAST._IExpr> _2029_arguments;
            _2029_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            while ((_2022_i) < (new BigInteger((_2021_generatedValues).Count))) {
              RAST._IExpr _2030_genKey;
              _2030_genKey = ((_2021_generatedValues).Select(_2022_i)).dtor__0;
              RAST._IExpr _2031_genValue;
              _2031_genValue = ((_2021_generatedValues).Select(_2022_i)).dtor__1;
              _2029_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2029_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(RAST.Expr.create_BinaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("=>"), _2030_genKey, _2031_genValue, DAST.Format.BinaryOpFormat.create_NoFormat())));
              _2022_i = (_2022_i) + (BigInteger.One);
            }
            r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("map!"))).Apply(_2029_arguments);
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
          DAST._IExpression _2032_expr = _source95.dtor_expr;
          DAST._IExpression _2033_index = _source95.dtor_indexExpr;
          DAST._IExpression _2034_value = _source95.dtor_value;
          unmatched95 = false;
          {
            RAST._IExpr _2035_exprR;
            DCOMP._IOwnership _2036___v176;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2037_exprIdents;
            RAST._IExpr _out435;
            DCOMP._IOwnership _out436;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out437;
            (this).GenExpr(_2032_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out435, out _out436, out _out437);
            _2035_exprR = _out435;
            _2036___v176 = _out436;
            _2037_exprIdents = _out437;
            RAST._IExpr _2038_indexR;
            DCOMP._IOwnership _2039_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2040_indexIdents;
            RAST._IExpr _out438;
            DCOMP._IOwnership _out439;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out440;
            (this).GenExpr(_2033_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out438, out _out439, out _out440);
            _2038_indexR = _out438;
            _2039_indexOwnership = _out439;
            _2040_indexIdents = _out440;
            RAST._IExpr _2041_valueR;
            DCOMP._IOwnership _2042_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2043_valueIdents;
            RAST._IExpr _out441;
            DCOMP._IOwnership _out442;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out443;
            (this).GenExpr(_2034_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out441, out _out442, out _out443);
            _2041_valueR = _out441;
            _2042_valueOwnership = _out442;
            _2043_valueIdents = _out443;
            r = ((_2035_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2038_indexR, _2041_valueR));
            RAST._IExpr _out444;
            DCOMP._IOwnership _out445;
            (this).FromOwned(r, expectedOwnership, out _out444, out _out445);
            r = _out444;
            resultingOwnership = _out445;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2037_exprIdents, _2040_indexIdents), _2043_valueIdents);
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapUpdate) {
          DAST._IExpression _2044_expr = _source95.dtor_expr;
          DAST._IExpression _2045_index = _source95.dtor_indexExpr;
          DAST._IExpression _2046_value = _source95.dtor_value;
          unmatched95 = false;
          {
            RAST._IExpr _2047_exprR;
            DCOMP._IOwnership _2048___v177;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2049_exprIdents;
            RAST._IExpr _out446;
            DCOMP._IOwnership _out447;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out448;
            (this).GenExpr(_2044_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out446, out _out447, out _out448);
            _2047_exprR = _out446;
            _2048___v177 = _out447;
            _2049_exprIdents = _out448;
            RAST._IExpr _2050_indexR;
            DCOMP._IOwnership _2051_indexOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2052_indexIdents;
            RAST._IExpr _out449;
            DCOMP._IOwnership _out450;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out451;
            (this).GenExpr(_2045_index, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out449, out _out450, out _out451);
            _2050_indexR = _out449;
            _2051_indexOwnership = _out450;
            _2052_indexIdents = _out451;
            RAST._IExpr _2053_valueR;
            DCOMP._IOwnership _2054_valueOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2055_valueIdents;
            RAST._IExpr _out452;
            DCOMP._IOwnership _out453;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out454;
            (this).GenExpr(_2046_value, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out452, out _out453, out _out454);
            _2053_valueR = _out452;
            _2054_valueOwnership = _out453;
            _2055_valueIdents = _out454;
            r = ((_2047_exprR).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("update_index"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2050_indexR, _2053_valueR));
            RAST._IExpr _out455;
            DCOMP._IOwnership _out456;
            (this).FromOwned(r, expectedOwnership, out _out455, out _out456);
            r = _out455;
            resultingOwnership = _out456;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2049_exprIdents, _2052_indexIdents), _2055_valueIdents);
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
                Dafny.ISequence<Dafny.Rune> _2056_id = _source96.dtor_rSelfName;
                DAST._IType _2057_dafnyType = _source96.dtor_dafnyType;
                unmatched96 = false;
                {
                  RAST._IExpr _out457;
                  DCOMP._IOwnership _out458;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out459;
                  (this).GenIdent(_2056_id, selfIdent, env, expectedOwnership, out _out457, out _out458, out _out459);
                  r = _out457;
                  resultingOwnership = _out458;
                  readIdents = _out459;
                }
              }
            }
            if (unmatched96) {
              DCOMP._ISelfInfo _2058_None = _source96;
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
          DAST._IExpression _2059_cond = _source95.dtor_cond;
          DAST._IExpression _2060_t = _source95.dtor_thn;
          DAST._IExpression _2061_f = _source95.dtor_els;
          unmatched95 = false;
          {
            RAST._IExpr _2062_cond;
            DCOMP._IOwnership _2063___v178;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2064_recIdentsCond;
            RAST._IExpr _out462;
            DCOMP._IOwnership _out463;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out464;
            (this).GenExpr(_2059_cond, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out462, out _out463, out _out464);
            _2062_cond = _out462;
            _2063___v178 = _out463;
            _2064_recIdentsCond = _out464;
            RAST._IExpr _2065_fExpr;
            DCOMP._IOwnership _2066_fOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2067_recIdentsF;
            RAST._IExpr _out465;
            DCOMP._IOwnership _out466;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out467;
            (this).GenExpr(_2061_f, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out465, out _out466, out _out467);
            _2065_fExpr = _out465;
            _2066_fOwned = _out466;
            _2067_recIdentsF = _out467;
            RAST._IExpr _2068_tExpr;
            DCOMP._IOwnership _2069___v179;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2070_recIdentsT;
            RAST._IExpr _out468;
            DCOMP._IOwnership _out469;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out470;
            (this).GenExpr(_2060_t, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out468, out _out469, out _out470);
            _2068_tExpr = _out468;
            _2069___v179 = _out469;
            _2070_recIdentsT = _out470;
            r = RAST.Expr.create_IfExpr(_2062_cond, _2068_tExpr, _2065_fExpr);
            RAST._IExpr _out471;
            DCOMP._IOwnership _out472;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out471, out _out472);
            r = _out471;
            resultingOwnership = _out472;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2064_recIdentsCond, _2070_recIdentsT), _2067_recIdentsF);
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnOp) {
          DAST._IUnaryOp unOp0 = _source95.dtor_unOp;
          if (unOp0.is_Not) {
            DAST._IExpression _2071_e = _source95.dtor_expr;
            DAST.Format._IUnaryOpFormat _2072_format = _source95.dtor_format1;
            unmatched95 = false;
            {
              RAST._IExpr _2073_recursiveGen;
              DCOMP._IOwnership _2074___v180;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2075_recIdents;
              RAST._IExpr _out473;
              DCOMP._IOwnership _out474;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out475;
              (this).GenExpr(_2071_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out473, out _out474, out _out475);
              _2073_recursiveGen = _out473;
              _2074___v180 = _out474;
              _2075_recIdents = _out475;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("!"), _2073_recursiveGen, _2072_format);
              RAST._IExpr _out476;
              DCOMP._IOwnership _out477;
              (this).FromOwned(r, expectedOwnership, out _out476, out _out477);
              r = _out476;
              resultingOwnership = _out477;
              readIdents = _2075_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnOp) {
          DAST._IUnaryOp unOp1 = _source95.dtor_unOp;
          if (unOp1.is_BitwiseNot) {
            DAST._IExpression _2076_e = _source95.dtor_expr;
            DAST.Format._IUnaryOpFormat _2077_format = _source95.dtor_format1;
            unmatched95 = false;
            {
              RAST._IExpr _2078_recursiveGen;
              DCOMP._IOwnership _2079___v181;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2080_recIdents;
              RAST._IExpr _out478;
              DCOMP._IOwnership _out479;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out480;
              (this).GenExpr(_2076_e, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out478, out _out479, out _out480);
              _2078_recursiveGen = _out478;
              _2079___v181 = _out479;
              _2080_recIdents = _out480;
              r = RAST.Expr.create_UnaryOp(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("~"), _2078_recursiveGen, _2077_format);
              RAST._IExpr _out481;
              DCOMP._IOwnership _out482;
              (this).FromOwned(r, expectedOwnership, out _out481, out _out482);
              r = _out481;
              resultingOwnership = _out482;
              readIdents = _2080_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnOp) {
          DAST._IUnaryOp unOp2 = _source95.dtor_unOp;
          if (unOp2.is_Cardinality) {
            DAST._IExpression _2081_e = _source95.dtor_expr;
            DAST.Format._IUnaryOpFormat _2082_format = _source95.dtor_format1;
            unmatched95 = false;
            {
              RAST._IExpr _2083_recursiveGen;
              DCOMP._IOwnership _2084_recOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2085_recIdents;
              RAST._IExpr _out483;
              DCOMP._IOwnership _out484;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out485;
              (this).GenExpr(_2081_e, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out483, out _out484, out _out485);
              _2083_recursiveGen = _out483;
              _2084_recOwned = _out484;
              _2085_recIdents = _out485;
              r = ((_2083_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("cardinality"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out486;
              DCOMP._IOwnership _out487;
              (this).FromOwned(r, expectedOwnership, out _out486, out _out487);
              r = _out486;
              resultingOwnership = _out487;
              readIdents = _2085_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_BinOp) {
          DAST._IBinOp _2086___v182 = _source95.dtor_op;
          DAST._IExpression _2087___v183 = _source95.dtor_left;
          DAST._IExpression _2088___v184 = _source95.dtor_right;
          DAST.Format._IBinaryOpFormat _2089___v185 = _source95.dtor_format2;
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
          DAST._IExpression _2090_expr = _source95.dtor_expr;
          DAST._IType _2091_exprType = _source95.dtor_exprType;
          BigInteger _2092_dim = _source95.dtor_dim;
          bool _2093_native = _source95.dtor_native;
          unmatched95 = false;
          {
            RAST._IExpr _2094_recursiveGen;
            DCOMP._IOwnership _2095___v186;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2096_recIdents;
            RAST._IExpr _out491;
            DCOMP._IOwnership _out492;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out493;
            (this).GenExpr(_2090_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out491, out _out492, out _out493);
            _2094_recursiveGen = _out491;
            _2095___v186 = _out492;
            _2096_recIdents = _out493;
            RAST._IType _2097_arrayType;
            RAST._IType _out494;
            _out494 = (this).GenType(_2091_exprType, DCOMP.GenTypeContext.@default());
            _2097_arrayType = _out494;
            if (!((_2097_arrayType).IsObjectOrPointer())) {
              Dafny.ISequence<Dafny.Rune> _2098_msg;
              _2098_msg = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Array length of something not an array but "), (_2097_arrayType)._ToString(DCOMP.__default.IND));
              (this).error = Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(_2098_msg);
              r = RAST.Expr.create_RawExpr(_2098_msg);
            } else {
              RAST._IType _2099_underlying;
              _2099_underlying = (_2097_arrayType).ObjectOrPointerUnderlying();
              if (((_2092_dim).Sign == 0) && ((_2099_underlying).is_Array)) {
                r = ((((this).read__macro).Apply1(_2094_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              } else {
                if ((_2092_dim).Sign == 0) {
                  r = (((((this).read__macro).Apply1(_2094_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("data"))).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("len"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
                } else {
                  r = (((this).read__macro).Apply1(_2094_recursiveGen)).Sel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Length"), Std.Strings.__default.OfNat(_2092_dim)));
                }
              }
              if (!(_2093_native)) {
                r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("int!"))).Apply1(r);
              }
            }
            RAST._IExpr _out495;
            DCOMP._IOwnership _out496;
            (this).FromOwned(r, expectedOwnership, out _out495, out _out496);
            r = _out495;
            resultingOwnership = _out496;
            readIdents = _2096_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapKeys) {
          DAST._IExpression _2100_expr = _source95.dtor_expr;
          unmatched95 = false;
          {
            RAST._IExpr _2101_recursiveGen;
            DCOMP._IOwnership _2102___v187;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2103_recIdents;
            RAST._IExpr _out497;
            DCOMP._IOwnership _out498;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out499;
            (this).GenExpr(_2100_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out497, out _out498, out _out499);
            _2101_recursiveGen = _out497;
            _2102___v187 = _out498;
            _2103_recIdents = _out499;
            readIdents = _2103_recIdents;
            r = ((_2101_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _2104_expr = _source95.dtor_expr;
          unmatched95 = false;
          {
            RAST._IExpr _2105_recursiveGen;
            DCOMP._IOwnership _2106___v188;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2107_recIdents;
            RAST._IExpr _out502;
            DCOMP._IOwnership _out503;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out504;
            (this).GenExpr(_2104_expr, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out502, out _out503, out _out504);
            _2105_recursiveGen = _out502;
            _2106___v188 = _out503;
            _2107_recIdents = _out504;
            readIdents = _2107_recIdents;
            r = ((_2105_recursiveGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("values"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IExpression _2108_on = _source95.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2109_field = _source95.dtor_field;
          bool _2110_isDatatype = _source95.dtor_onDatatype;
          bool _2111_isStatic = _source95.dtor_isStatic;
          BigInteger _2112_arity = _source95.dtor_arity;
          unmatched95 = false;
          {
            RAST._IExpr _2113_onExpr;
            DCOMP._IOwnership _2114_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2115_recIdents;
            RAST._IExpr _out507;
            DCOMP._IOwnership _out508;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out509;
            (this).GenExpr(_2108_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out507, out _out508, out _out509);
            _2113_onExpr = _out507;
            _2114_onOwned = _out508;
            _2115_recIdents = _out509;
            Dafny.ISequence<Dafny.Rune> _2116_s = Dafny.Sequence<Dafny.Rune>.Empty;
            Dafny.ISequence<Dafny.Rune> _2117_onString;
            _2117_onString = (_2113_onExpr)._ToString(DCOMP.__default.IND);
            if (_2111_isStatic) {
              _2116_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2117_onString, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::")), DCOMP.__default.escapeName(_2109_field));
            } else {
              _2116_s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{\n");
              _2116_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2116_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("let callTarget = (")), _2117_onString), ((object.Equals(_2114_onOwned, DCOMP.Ownership.create_OwnershipOwned())) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString(").clone()")))), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(";\n"));
              Dafny.ISequence<Dafny.Rune> _2118_args;
              _2118_args = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("");
              BigInteger _2119_i;
              _2119_i = BigInteger.Zero;
              while ((_2119_i) < (_2112_arity)) {
                if ((_2119_i).Sign == 1) {
                  _2118_args = Dafny.Sequence<Dafny.Rune>.Concat(_2118_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
                }
                _2118_args = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2118_args, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("arg")), Std.Strings.__default.OfNat(_2119_i));
                _2119_i = (_2119_i) + (BigInteger.One);
              }
              _2116_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2116_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("move |")), _2118_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("| {\n"));
              _2116_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(_2116_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("callTarget.")), DCOMP.__default.escapeName(_2109_field)), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("(")), _2118_args), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(")\n"));
              _2116_s = Dafny.Sequence<Dafny.Rune>.Concat(_2116_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}\n"));
              _2116_s = Dafny.Sequence<Dafny.Rune>.Concat(_2116_s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("}"));
            }
            Dafny.ISequence<Dafny.Rune> _2120_typeShape;
            _2120_typeShape = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("dyn ::std::ops::Fn(");
            BigInteger _2121_i;
            _2121_i = BigInteger.Zero;
            while ((_2121_i) < (_2112_arity)) {
              if ((_2121_i).Sign == 1) {
                _2120_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2120_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(", "));
              }
              _2120_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2120_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&_"));
              _2121_i = (_2121_i) + (BigInteger.One);
            }
            _2120_typeShape = Dafny.Sequence<Dafny.Rune>.Concat(_2120_typeShape, Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") -> _"));
            _2116_s = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::std::rc::Rc::new("), _2116_s), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(") as ::std::rc::Rc<")), _2120_typeShape), Dafny.Sequence<Dafny.Rune>.UnicodeFromString(">"));
            r = RAST.Expr.create_RawExpr(_2116_s);
            RAST._IExpr _out510;
            DCOMP._IOwnership _out511;
            (this).FromOwned(r, expectedOwnership, out _out510, out _out511);
            r = _out510;
            resultingOwnership = _out511;
            readIdents = _2115_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Select) {
          DAST._IExpression expr0 = _source95.dtor_expr;
          if (expr0.is_Companion) {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2122_c = expr0.dtor_Companion_a0;
            Dafny.ISequence<DAST._IType> _2123_typeArgs = expr0.dtor_typeArgs;
            Dafny.ISequence<Dafny.Rune> _2124_field = _source95.dtor_field;
            bool _2125_isConstant = _source95.dtor_isConstant;
            bool _2126_isDatatype = _source95.dtor_onDatatype;
            DAST._IType _2127_fieldType = _source95.dtor_fieldType;
            unmatched95 = false;
            {
              RAST._IExpr _2128_onExpr;
              DCOMP._IOwnership _2129_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2130_recIdents;
              RAST._IExpr _out512;
              DCOMP._IOwnership _out513;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out514;
              (this).GenExpr(DAST.Expression.create_Companion(_2122_c, _2123_typeArgs), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out512, out _out513, out _out514);
              _2128_onExpr = _out512;
              _2129_onOwned = _out513;
              _2130_recIdents = _out514;
              r = ((_2128_onExpr).MSel(DCOMP.__default.escapeName(_2124_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IExpr _out515;
              DCOMP._IOwnership _out516;
              (this).FromOwned(r, expectedOwnership, out _out515, out _out516);
              r = _out515;
              resultingOwnership = _out516;
              readIdents = _2130_recIdents;
              return ;
            }
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Select) {
          DAST._IExpression _2131_on = _source95.dtor_expr;
          Dafny.ISequence<Dafny.Rune> _2132_field = _source95.dtor_field;
          bool _2133_isConstant = _source95.dtor_isConstant;
          bool _2134_isDatatype = _source95.dtor_onDatatype;
          DAST._IType _2135_fieldType = _source95.dtor_fieldType;
          unmatched95 = false;
          {
            if (_2134_isDatatype) {
              RAST._IExpr _2136_onExpr;
              DCOMP._IOwnership _2137_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2138_recIdents;
              RAST._IExpr _out517;
              DCOMP._IOwnership _out518;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out519;
              (this).GenExpr(_2131_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out517, out _out518, out _out519);
              _2136_onExpr = _out517;
              _2137_onOwned = _out518;
              _2138_recIdents = _out519;
              r = ((_2136_onExpr).Sel(DCOMP.__default.escapeName(_2132_field))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              RAST._IType _2139_typ;
              RAST._IType _out520;
              _out520 = (this).GenType(_2135_fieldType, DCOMP.GenTypeContext.@default());
              _2139_typ = _out520;
              RAST._IExpr _out521;
              DCOMP._IOwnership _out522;
              (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipBorrowed(), expectedOwnership, out _out521, out _out522);
              r = _out521;
              resultingOwnership = _out522;
              readIdents = _2138_recIdents;
            } else {
              RAST._IExpr _2140_onExpr;
              DCOMP._IOwnership _2141_onOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2142_recIdents;
              RAST._IExpr _out523;
              DCOMP._IOwnership _out524;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out525;
              (this).GenExpr(_2131_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out523, out _out524, out _out525);
              _2140_onExpr = _out523;
              _2141_onOwned = _out524;
              _2142_recIdents = _out525;
              r = _2140_onExpr;
              if (!object.Equals(_2140_onExpr, RAST.__default.self)) {
                RAST._IExpr _source97 = _2140_onExpr;
                bool unmatched97 = true;
                if (unmatched97) {
                  if (_source97.is_UnaryOp) {
                    Dafny.ISequence<Dafny.Rune> op15 = _source97.dtor_op1;
                    if (object.Equals(op15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("&"))) {
                      RAST._IExpr underlying5 = _source97.dtor_underlying;
                      if (underlying5.is_Identifier) {
                        Dafny.ISequence<Dafny.Rune> name15 = underlying5.dtor_name;
                        if (object.Equals(name15, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"))) {
                          DAST.Format._IUnaryOpFormat _2143___v189 = _source97.dtor_format;
                          unmatched97 = false;
                          r = RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("this"));
                        }
                      }
                    }
                  }
                }
                if (unmatched97) {
                  RAST._IExpr _2144___v190 = _source97;
                  unmatched97 = false;
                }
                if (((this).ObjectType).is_RcMut) {
                  r = (r).Clone();
                }
                r = ((this).read__macro).Apply1(r);
              }
              r = (r).Sel(DCOMP.__default.escapeName(_2132_field));
              if (_2133_isConstant) {
                r = (r).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              r = (r).Clone();
              RAST._IExpr _out526;
              DCOMP._IOwnership _out527;
              (this).FromOwned(r, expectedOwnership, out _out526, out _out527);
              r = _out526;
              resultingOwnership = _out527;
              readIdents = _2142_recIdents;
            }
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Index) {
          DAST._IExpression _2145_on = _source95.dtor_expr;
          DAST._ICollKind _2146_collKind = _source95.dtor_collKind;
          Dafny.ISequence<DAST._IExpression> _2147_indices = _source95.dtor_indices;
          unmatched95 = false;
          {
            RAST._IExpr _2148_onExpr;
            DCOMP._IOwnership _2149_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2150_recIdents;
            RAST._IExpr _out528;
            DCOMP._IOwnership _out529;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out530;
            (this).GenExpr(_2145_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out528, out _out529, out _out530);
            _2148_onExpr = _out528;
            _2149_onOwned = _out529;
            _2150_recIdents = _out530;
            readIdents = _2150_recIdents;
            r = _2148_onExpr;
            BigInteger _2151_i;
            _2151_i = BigInteger.Zero;
            while ((_2151_i) < (new BigInteger((_2147_indices).Count))) {
              if (object.Equals(_2146_collKind, DAST.CollKind.create_Array())) {
                r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("borrow"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
              }
              RAST._IExpr _2152_idx;
              DCOMP._IOwnership _2153_idxOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2154_recIdentsIdx;
              RAST._IExpr _out531;
              DCOMP._IOwnership _out532;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out533;
              (this).GenExpr((_2147_indices).Select(_2151_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out531, out _out532, out _out533);
              _2152_idx = _out531;
              _2153_idxOwned = _out532;
              _2154_recIdentsIdx = _out533;
              r = ((r).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("get"))).Apply1(_2152_idx);
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2154_recIdentsIdx);
              _2151_i = (_2151_i) + (BigInteger.One);
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
          DAST._IExpression _2155_on = _source95.dtor_expr;
          bool _2156_isArray = _source95.dtor_isArray;
          Std.Wrappers._IOption<DAST._IExpression> _2157_low = _source95.dtor_low;
          Std.Wrappers._IOption<DAST._IExpression> _2158_high = _source95.dtor_high;
          unmatched95 = false;
          {
            RAST._IExpr _2159_onExpr;
            DCOMP._IOwnership _2160_onOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2161_recIdents;
            RAST._IExpr _out536;
            DCOMP._IOwnership _out537;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out538;
            (this).GenExpr(_2155_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out536, out _out537, out _out538);
            _2159_onExpr = _out536;
            _2160_onOwned = _out537;
            _2161_recIdents = _out538;
            readIdents = _2161_recIdents;
            Dafny.ISequence<Dafny.Rune> _2162_methodName;
            _2162_methodName = (((_2157_low).is_Some) ? ((((_2158_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("slice")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("drop")))) : ((((_2158_high).is_Some) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("take")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")))));
            Dafny.ISequence<RAST._IExpr> _2163_arguments;
            _2163_arguments = Dafny.Sequence<RAST._IExpr>.FromElements();
            Std.Wrappers._IOption<DAST._IExpression> _source98 = _2157_low;
            bool unmatched98 = true;
            if (unmatched98) {
              if (_source98.is_Some) {
                DAST._IExpression _2164_l = _source98.dtor_value;
                unmatched98 = false;
                {
                  RAST._IExpr _2165_lExpr;
                  DCOMP._IOwnership _2166___v191;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2167_recIdentsL;
                  RAST._IExpr _out539;
                  DCOMP._IOwnership _out540;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out541;
                  (this).GenExpr(_2164_l, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out539, out _out540, out _out541);
                  _2165_lExpr = _out539;
                  _2166___v191 = _out540;
                  _2167_recIdentsL = _out541;
                  _2163_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2163_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2165_lExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2167_recIdentsL);
                }
              }
            }
            if (unmatched98) {
              unmatched98 = false;
            }
            Std.Wrappers._IOption<DAST._IExpression> _source99 = _2158_high;
            bool unmatched99 = true;
            if (unmatched99) {
              if (_source99.is_Some) {
                DAST._IExpression _2168_h = _source99.dtor_value;
                unmatched99 = false;
                {
                  RAST._IExpr _2169_hExpr;
                  DCOMP._IOwnership _2170___v192;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2171_recIdentsH;
                  RAST._IExpr _out542;
                  DCOMP._IOwnership _out543;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out544;
                  (this).GenExpr(_2168_h, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out542, out _out543, out _out544);
                  _2169_hExpr = _out542;
                  _2170___v192 = _out543;
                  _2171_recIdentsH = _out544;
                  _2163_arguments = Dafny.Sequence<RAST._IExpr>.Concat(_2163_arguments, Dafny.Sequence<RAST._IExpr>.FromElements(_2169_hExpr));
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2171_recIdentsH);
                }
              }
            }
            if (unmatched99) {
              unmatched99 = false;
            }
            r = _2159_onExpr;
            if (_2156_isArray) {
              if (!(_2162_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                _2162_methodName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2162_methodName);
              }
              r = ((RAST.__default.dafny__runtime__Sequence).MSel(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("from_array"), _2162_methodName))).Apply(_2163_arguments);
            } else {
              if (!(_2162_methodName).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""))) {
                r = ((r).Sel(_2162_methodName)).Apply(_2163_arguments);
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
          DAST._IExpression _2172_on = _source95.dtor_expr;
          BigInteger _2173_idx = _source95.dtor_index;
          DAST._IType _2174_fieldType = _source95.dtor_fieldType;
          unmatched95 = false;
          {
            RAST._IExpr _2175_onExpr;
            DCOMP._IOwnership _2176_onOwnership;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2177_recIdents;
            RAST._IExpr _out547;
            DCOMP._IOwnership _out548;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out549;
            (this).GenExpr(_2172_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out547, out _out548, out _out549);
            _2175_onExpr = _out547;
            _2176_onOwnership = _out548;
            _2177_recIdents = _out549;
            Dafny.ISequence<Dafny.Rune> _2178_selName;
            _2178_selName = Std.Strings.__default.OfNat(_2173_idx);
            DAST._IType _source100 = _2174_fieldType;
            bool unmatched100 = true;
            if (unmatched100) {
              if (_source100.is_Tuple) {
                Dafny.ISequence<DAST._IType> _2179_tps = _source100.dtor_Tuple_a0;
                unmatched100 = false;
                if (((_2174_fieldType).is_Tuple) && ((new BigInteger((_2179_tps).Count)) > (RAST.__default.MAX__TUPLE__SIZE))) {
                  _2178_selName = Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_"), _2178_selName);
                }
              }
            }
            if (unmatched100) {
              DAST._IType _2180___v193 = _source100;
              unmatched100 = false;
            }
            r = (_2175_onExpr).Sel(_2178_selName);
            RAST._IExpr _out550;
            DCOMP._IOwnership _out551;
            (this).FromOwnership(r, DCOMP.Ownership.create_OwnershipOwned(), expectedOwnership, out _out550, out _out551);
            r = _out550;
            resultingOwnership = _out551;
            readIdents = _2177_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_Call) {
          DAST._IExpression _2181_on = _source95.dtor_on;
          DAST._ICallName _2182_name = _source95.dtor_callName;
          Dafny.ISequence<DAST._IType> _2183_typeArgs = _source95.dtor_typeArgs;
          Dafny.ISequence<DAST._IExpression> _2184_args = _source95.dtor_args;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IExpr> _2185_argExprs;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2186_recIdents;
            Dafny.ISequence<RAST._IType> _2187_typeExprs;
            Std.Wrappers._IOption<DAST._IResolvedType> _2188_fullNameQualifier;
            Dafny.ISequence<RAST._IExpr> _out552;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out553;
            Dafny.ISequence<RAST._IType> _out554;
            Std.Wrappers._IOption<DAST._IResolvedType> _out555;
            (this).GenArgs(selfIdent, _2182_name, _2183_typeArgs, _2184_args, env, out _out552, out _out553, out _out554, out _out555);
            _2185_argExprs = _out552;
            _2186_recIdents = _out553;
            _2187_typeExprs = _out554;
            _2188_fullNameQualifier = _out555;
            readIdents = _2186_recIdents;
            Std.Wrappers._IOption<DAST._IResolvedType> _source101 = _2188_fullNameQualifier;
            bool unmatched101 = true;
            if (unmatched101) {
              if (_source101.is_Some) {
                DAST._IResolvedType value11 = _source101.dtor_value;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2189_path = value11.dtor_path;
                Dafny.ISequence<DAST._IType> _2190_onTypeArgs = value11.dtor_typeArgs;
                DAST._IResolvedTypeBase _2191_base = value11.dtor_kind;
                Dafny.ISequence<DAST._IAttribute> _2192___v194 = value11.dtor_attributes;
                Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2193___v195 = value11.dtor_properMethods;
                Dafny.ISequence<DAST._IType> _2194___v196 = value11.dtor_extendedTypes;
                unmatched101 = false;
                RAST._IExpr _2195_fullPath;
                RAST._IExpr _out556;
                _out556 = DCOMP.COMP.GenPathExpr(_2189_path);
                _2195_fullPath = _out556;
                Dafny.ISequence<RAST._IType> _2196_onTypeExprs;
                Dafny.ISequence<RAST._IType> _out557;
                _out557 = (this).GenTypeArgs(_2190_onTypeArgs, DCOMP.GenTypeContext.@default());
                _2196_onTypeExprs = _out557;
                RAST._IExpr _2197_onExpr = RAST.Expr.Default();
                DCOMP._IOwnership _2198_recOwnership = DCOMP.Ownership.Default();
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2199_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Empty;
                if (((_2191_base).is_Trait) || ((_2191_base).is_Class)) {
                  RAST._IExpr _out558;
                  DCOMP._IOwnership _out559;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out560;
                  (this).GenExpr(_2181_on, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out558, out _out559, out _out560);
                  _2197_onExpr = _out558;
                  _2198_recOwnership = _out559;
                  _2199_recIdents = _out560;
                  _2197_onExpr = ((this).read__macro).Apply1(_2197_onExpr);
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2199_recIdents);
                } else {
                  RAST._IExpr _out561;
                  DCOMP._IOwnership _out562;
                  Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out563;
                  (this).GenExpr(_2181_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out561, out _out562, out _out563);
                  _2197_onExpr = _out561;
                  _2198_recOwnership = _out562;
                  _2199_recIdents = _out563;
                  readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2199_recIdents);
                }
                r = ((((_2195_fullPath).ApplyType(_2196_onTypeExprs)).MSel(DCOMP.__default.escapeName((_2182_name).dtor_name))).ApplyType(_2187_typeExprs)).Apply(Dafny.Sequence<RAST._IExpr>.Concat(Dafny.Sequence<RAST._IExpr>.FromElements(_2197_onExpr), _2185_argExprs));
                RAST._IExpr _out564;
                DCOMP._IOwnership _out565;
                (this).FromOwned(r, expectedOwnership, out _out564, out _out565);
                r = _out564;
                resultingOwnership = _out565;
              }
            }
            if (unmatched101) {
              Std.Wrappers._IOption<DAST._IResolvedType> _2200___v197 = _source101;
              unmatched101 = false;
              RAST._IExpr _2201_onExpr;
              DCOMP._IOwnership _2202___v198;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2203_recIdents;
              RAST._IExpr _out566;
              DCOMP._IOwnership _out567;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out568;
              (this).GenExpr(_2181_on, selfIdent, env, DCOMP.Ownership.create_OwnershipAutoBorrowed(), out _out566, out _out567, out _out568);
              _2201_onExpr = _out566;
              _2202___v198 = _out567;
              _2203_recIdents = _out568;
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2203_recIdents);
              Dafny.ISequence<Dafny.Rune> _2204_renderedName;
              _2204_renderedName = ((System.Func<Dafny.ISequence<Dafny.Rune>>)(() => {
                DAST._ICallName _source102 = _2182_name;
                bool unmatched102 = true;
                if (unmatched102) {
                  if (_source102.is_CallName) {
                    Dafny.ISequence<Dafny.Rune> _2205_ident = _source102.dtor_name;
                    Std.Wrappers._IOption<DAST._IType> _2206___v199 = _source102.dtor_onType;
                    Std.Wrappers._IOption<DAST._IFormal> _2207___v200 = _source102.dtor_receiverArgs;
                    Dafny.ISequence<DAST._IFormal> _2208___v201 = _source102.dtor_signature;
                    unmatched102 = false;
                    return DCOMP.__default.escapeName(_2205_ident);
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
              DAST._IExpression _source103 = _2181_on;
              bool unmatched103 = true;
              if (unmatched103) {
                if (_source103.is_Companion) {
                  Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2209___v202 = _source103.dtor_Companion_a0;
                  Dafny.ISequence<DAST._IType> _2210___v203 = _source103.dtor_typeArgs;
                  unmatched103 = false;
                  {
                    _2201_onExpr = (_2201_onExpr).MSel(_2204_renderedName);
                  }
                }
              }
              if (unmatched103) {
                DAST._IExpression _2211___v204 = _source103;
                unmatched103 = false;
                {
                  if (!object.Equals(_2201_onExpr, RAST.__default.self)) {
                    DAST._ICallName _source104 = _2182_name;
                    bool unmatched104 = true;
                    if (unmatched104) {
                      if (_source104.is_CallName) {
                        Dafny.ISequence<Dafny.Rune> _2212___v205 = _source104.dtor_name;
                        Std.Wrappers._IOption<DAST._IType> onType2 = _source104.dtor_onType;
                        if (onType2.is_Some) {
                          DAST._IType _2213_tpe = onType2.dtor_value;
                          Std.Wrappers._IOption<DAST._IFormal> _2214___v206 = _source104.dtor_receiverArgs;
                          Dafny.ISequence<DAST._IFormal> _2215___v207 = _source104.dtor_signature;
                          unmatched104 = false;
                          RAST._IType _2216_typ;
                          RAST._IType _out569;
                          _out569 = (this).GenType(_2213_tpe, DCOMP.GenTypeContext.@default());
                          _2216_typ = _out569;
                          if ((_2216_typ).IsObjectOrPointer()) {
                            _2201_onExpr = ((this).read__macro).Apply1(_2201_onExpr);
                          }
                        }
                      }
                    }
                    if (unmatched104) {
                      DAST._ICallName _2217___v208 = _source104;
                      unmatched104 = false;
                    }
                  }
                  _2201_onExpr = (_2201_onExpr).Sel(_2204_renderedName);
                }
              }
              r = ((_2201_onExpr).ApplyType(_2187_typeExprs)).Apply(_2185_argExprs);
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
          Dafny.ISequence<DAST._IFormal> _2218_paramsDafny = _source95.dtor_params;
          DAST._IType _2219_retType = _source95.dtor_retType;
          Dafny.ISequence<DAST._IStatement> _2220_body = _source95.dtor_body;
          unmatched95 = false;
          {
            Dafny.ISequence<RAST._IFormal> _2221_params;
            Dafny.ISequence<RAST._IFormal> _out572;
            _out572 = (this).GenParams(_2218_paramsDafny);
            _2221_params = _out572;
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2222_paramNames;
            _2222_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2223_paramTypesMap;
            _2223_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            BigInteger _hi45 = new BigInteger((_2221_params).Count);
            for (BigInteger _2224_i = BigInteger.Zero; _2224_i < _hi45; _2224_i++) {
              Dafny.ISequence<Dafny.Rune> _2225_name;
              _2225_name = ((_2221_params).Select(_2224_i)).dtor_name;
              _2222_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2222_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2225_name));
              _2223_paramTypesMap = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2223_paramTypesMap, _2225_name, ((_2221_params).Select(_2224_i)).dtor_tpe);
            }
            DCOMP._IEnvironment _2226_subEnv;
            _2226_subEnv = ((env).ToOwned()).merge(DCOMP.Environment.create(_2222_paramNames, _2223_paramTypesMap));
            RAST._IExpr _2227_recursiveGen;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2228_recIdents;
            DCOMP._IEnvironment _2229___v209;
            RAST._IExpr _out573;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out574;
            DCOMP._IEnvironment _out575;
            (this).GenStmts(_2220_body, ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) ? (DCOMP.SelfInfo.create_ThisTyped(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), (selfIdent).dtor_dafnyType)) : (DCOMP.SelfInfo.create_NoSelf())), _2226_subEnv, true, RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("")), out _out573, out _out574, out _out575);
            _2227_recursiveGen = _out573;
            _2228_recIdents = _out574;
            _2229___v209 = _out575;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            _2228_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2228_recIdents, Dafny.Helpers.Id<Func<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>, Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>>((_2230_paramNames) => ((System.Func<Dafny.ISet<Dafny.ISequence<Dafny.Rune>>>)(() => {
              var _coll7 = new System.Collections.Generic.List<Dafny.ISequence<Dafny.Rune>>();
              foreach (Dafny.ISequence<Dafny.Rune> _compr_7 in (_2230_paramNames).CloneAsArray()) {
                Dafny.ISequence<Dafny.Rune> _2231_name = (Dafny.ISequence<Dafny.Rune>)_compr_7;
                if ((_2230_paramNames).Contains(_2231_name)) {
                  _coll7.Add(_2231_name);
                }
              }
              return Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromCollection(_coll7);
            }))())(_2222_paramNames));
            RAST._IExpr _2232_allReadCloned;
            _2232_allReadCloned = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            while (!(_2228_recIdents).Equals(Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements())) {
              Dafny.ISequence<Dafny.Rune> _2233_next;
              foreach (Dafny.ISequence<Dafny.Rune> _assign_such_that_3 in (_2228_recIdents).Elements) {
                _2233_next = (Dafny.ISequence<Dafny.Rune>)_assign_such_that_3;
                if ((_2228_recIdents).Contains(_2233_next)) {
                  goto after__ASSIGN_SUCH_THAT_3;
                }
              }
              throw new System.Exception("assign-such-that search produced no value (line 4767)");
            after__ASSIGN_SUCH_THAT_3: ;
              if ((!object.Equals(selfIdent, DCOMP.SelfInfo.create_NoSelf())) && ((_2233_next).Equals(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this")))) {
                RAST._IExpr _2234_selfCloned;
                DCOMP._IOwnership _2235___v210;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2236___v211;
                RAST._IExpr _out576;
                DCOMP._IOwnership _out577;
                Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out578;
                (this).GenIdent(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("self"), selfIdent, DCOMP.Environment.Empty(), DCOMP.Ownership.create_OwnershipOwned(), out _out576, out _out577, out _out578);
                _2234_selfCloned = _out576;
                _2235___v210 = _out577;
                _2236___v211 = _out578;
                _2232_allReadCloned = (_2232_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("_this"), Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2234_selfCloned)));
              } else if (!((_2222_paramNames).Contains(_2233_next))) {
                RAST._IExpr _2237_copy;
                _2237_copy = (RAST.Expr.create_Identifier(_2233_next)).Clone();
                _2232_allReadCloned = (_2232_allReadCloned).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_MUT(), _2233_next, Std.Wrappers.Option<RAST._IType>.create_None(), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2237_copy)));
                readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2233_next));
              }
              _2228_recIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2228_recIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2233_next));
            }
            RAST._IType _2238_retTypeGen;
            RAST._IType _out579;
            _out579 = (this).GenType(_2219_retType, DCOMP.GenTypeContext.InFn());
            _2238_retTypeGen = _out579;
            r = RAST.Expr.create_Block((_2232_allReadCloned).Then(RAST.__default.RcNew(RAST.Expr.create_Lambda(_2221_params, Std.Wrappers.Option<RAST._IType>.create_Some(_2238_retTypeGen), RAST.Expr.create_Block(_2227_recursiveGen)))));
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
          Dafny.ISequence<_System._ITuple2<DAST._IFormal, DAST._IExpression>> _2239_values = _source95.dtor_values;
          DAST._IType _2240_retType = _source95.dtor_retType;
          DAST._IExpression _2241_expr = _source95.dtor_expr;
          unmatched95 = false;
          {
            Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2242_paramNames;
            _2242_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements();
            Dafny.ISequence<RAST._IFormal> _2243_paramFormals;
            Dafny.ISequence<RAST._IFormal> _out582;
            _out582 = (this).GenParams(Std.Collections.Seq.__default.Map<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>(((System.Func<_System._ITuple2<DAST._IFormal, DAST._IExpression>, DAST._IFormal>)((_2244_value) => {
              return (_2244_value).dtor__0;
            })), _2239_values));
            _2243_paramFormals = _out582;
            Dafny.IMap<Dafny.ISequence<Dafny.Rune>,RAST._IType> _2245_paramTypes;
            _2245_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.FromElements();
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2246_paramNamesSet;
            _2246_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            BigInteger _hi46 = new BigInteger((_2239_values).Count);
            for (BigInteger _2247_i = BigInteger.Zero; _2247_i < _hi46; _2247_i++) {
              Dafny.ISequence<Dafny.Rune> _2248_name;
              _2248_name = (((_2239_values).Select(_2247_i)).dtor__0).dtor_name;
              Dafny.ISequence<Dafny.Rune> _2249_rName;
              _2249_rName = DCOMP.__default.escapeName(_2248_name);
              _2242_paramNames = Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.Concat(_2242_paramNames, Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements(_2249_rName));
              _2245_paramTypes = Dafny.Map<Dafny.ISequence<Dafny.Rune>, RAST._IType>.Update(_2245_paramTypes, _2249_rName, ((_2243_paramFormals).Select(_2247_i)).dtor_tpe);
              _2246_paramNamesSet = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2246_paramNamesSet, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(_2249_rName));
            }
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
            BigInteger _hi47 = new BigInteger((_2239_values).Count);
            for (BigInteger _2250_i = BigInteger.Zero; _2250_i < _hi47; _2250_i++) {
              RAST._IType _2251_typeGen;
              RAST._IType _out583;
              _out583 = (this).GenType((((_2239_values).Select(_2250_i)).dtor__0).dtor_typ, DCOMP.GenTypeContext.InFn());
              _2251_typeGen = _out583;
              RAST._IExpr _2252_valueGen;
              DCOMP._IOwnership _2253___v212;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2254_recIdents;
              RAST._IExpr _out584;
              DCOMP._IOwnership _out585;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out586;
              (this).GenExpr(((_2239_values).Select(_2250_i)).dtor__1, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out584, out _out585, out _out586);
              _2252_valueGen = _out584;
              _2253___v212 = _out585;
              _2254_recIdents = _out586;
              r = (r).Then(RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((((_2239_values).Select(_2250_i)).dtor__0).dtor_name), Std.Wrappers.Option<RAST._IType>.create_Some(_2251_typeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2252_valueGen)));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2254_recIdents);
            }
            DCOMP._IEnvironment _2255_newEnv;
            _2255_newEnv = DCOMP.Environment.create(_2242_paramNames, _2245_paramTypes);
            RAST._IExpr _2256_recGen;
            DCOMP._IOwnership _2257_recOwned;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2258_recIdents;
            RAST._IExpr _out587;
            DCOMP._IOwnership _out588;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out589;
            (this).GenExpr(_2241_expr, selfIdent, _2255_newEnv, expectedOwnership, out _out587, out _out588, out _out589);
            _2256_recGen = _out587;
            _2257_recOwned = _out588;
            _2258_recIdents = _out589;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2258_recIdents, _2246_paramNamesSet);
            r = RAST.Expr.create_Block((r).Then(_2256_recGen));
            RAST._IExpr _out590;
            DCOMP._IOwnership _out591;
            (this).FromOwnership(r, _2257_recOwned, expectedOwnership, out _out590, out _out591);
            r = _out590;
            resultingOwnership = _out591;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_IIFE) {
          Dafny.ISequence<Dafny.Rune> _2259_name = _source95.dtor_name;
          DAST._IType _2260_tpe = _source95.dtor_typ;
          DAST._IExpression _2261_value = _source95.dtor_value;
          DAST._IExpression _2262_iifeBody = _source95.dtor_iifeBody;
          unmatched95 = false;
          {
            RAST._IExpr _2263_valueGen;
            DCOMP._IOwnership _2264___v213;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2265_recIdents;
            RAST._IExpr _out592;
            DCOMP._IOwnership _out593;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out594;
            (this).GenExpr(_2261_value, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out592, out _out593, out _out594);
            _2263_valueGen = _out592;
            _2264___v213 = _out593;
            _2265_recIdents = _out594;
            readIdents = _2265_recIdents;
            RAST._IType _2266_valueTypeGen;
            RAST._IType _out595;
            _out595 = (this).GenType(_2260_tpe, DCOMP.GenTypeContext.InFn());
            _2266_valueTypeGen = _out595;
            RAST._IExpr _2267_bodyGen;
            DCOMP._IOwnership _2268___v214;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2269_bodyIdents;
            RAST._IExpr _out596;
            DCOMP._IOwnership _out597;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out598;
            (this).GenExpr(_2262_iifeBody, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out596, out _out597, out _out598);
            _2267_bodyGen = _out596;
            _2268___v214 = _out597;
            _2269_bodyIdents = _out598;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Difference(_2269_bodyIdents, Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements(DCOMP.__default.escapeName((_2259_name)))));
            r = RAST.Expr.create_Block((RAST.Expr.create_DeclareVar(RAST.DeclareType.create_CONST(), DCOMP.__default.escapeName((_2259_name)), Std.Wrappers.Option<RAST._IType>.create_Some(_2266_valueTypeGen), Std.Wrappers.Option<RAST._IExpr>.create_Some(_2263_valueGen))).Then(_2267_bodyGen));
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
          DAST._IExpression _2270_func = _source95.dtor_expr;
          Dafny.ISequence<DAST._IExpression> _2271_args = _source95.dtor_args;
          unmatched95 = false;
          {
            RAST._IExpr _2272_funcExpr;
            DCOMP._IOwnership _2273___v215;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2274_recIdents;
            RAST._IExpr _out601;
            DCOMP._IOwnership _out602;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out603;
            (this).GenExpr(_2270_func, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out601, out _out602, out _out603);
            _2272_funcExpr = _out601;
            _2273___v215 = _out602;
            _2274_recIdents = _out603;
            readIdents = _2274_recIdents;
            Dafny.ISequence<RAST._IExpr> _2275_rArgs;
            _2275_rArgs = Dafny.Sequence<RAST._IExpr>.FromElements();
            BigInteger _hi48 = new BigInteger((_2271_args).Count);
            for (BigInteger _2276_i = BigInteger.Zero; _2276_i < _hi48; _2276_i++) {
              RAST._IExpr _2277_argExpr;
              DCOMP._IOwnership _2278_argOwned;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2279_argIdents;
              RAST._IExpr _out604;
              DCOMP._IOwnership _out605;
              Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out606;
              (this).GenExpr((_2271_args).Select(_2276_i), selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out604, out _out605, out _out606);
              _2277_argExpr = _out604;
              _2278_argOwned = _out605;
              _2279_argIdents = _out606;
              _2275_rArgs = Dafny.Sequence<RAST._IExpr>.Concat(_2275_rArgs, Dafny.Sequence<RAST._IExpr>.FromElements(_2277_argExpr));
              readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(readIdents, _2279_argIdents);
            }
            r = (_2272_funcExpr).Apply(_2275_rArgs);
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
          DAST._IExpression _2280_on = _source95.dtor_on;
          Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> _2281_dType = _source95.dtor_dType;
          Dafny.ISequence<Dafny.Rune> _2282_variant = _source95.dtor_variant;
          unmatched95 = false;
          {
            RAST._IExpr _2283_exprGen;
            DCOMP._IOwnership _2284___v216;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2285_recIdents;
            RAST._IExpr _out609;
            DCOMP._IOwnership _out610;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out611;
            (this).GenExpr(_2280_on, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out609, out _out610, out _out611);
            _2283_exprGen = _out609;
            _2284___v216 = _out610;
            _2285_recIdents = _out611;
            RAST._IType _2286_dTypePath;
            RAST._IType _out612;
            _out612 = DCOMP.COMP.GenPath(_2281_dType);
            _2286_dTypePath = _out612;
            r = (RAST.Expr.create_Identifier(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("matches!"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(((_2283_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()), RAST.Expr.create_RawExpr(Dafny.Sequence<Dafny.Rune>.Concat(((_2286_dTypePath).MSel(DCOMP.__default.escapeName(_2282_variant)))._ToString(DCOMP.__default.IND), Dafny.Sequence<Dafny.Rune>.UnicodeFromString("{ .. }")))));
            RAST._IExpr _out613;
            DCOMP._IOwnership _out614;
            (this).FromOwned(r, expectedOwnership, out _out613, out _out614);
            r = _out613;
            resultingOwnership = _out614;
            readIdents = _2285_recIdents;
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
          DAST._IExpression _2287_of = _source95.dtor_of;
          unmatched95 = false;
          {
            RAST._IExpr _2288_exprGen;
            DCOMP._IOwnership _2289___v217;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2290_recIdents;
            RAST._IExpr _out617;
            DCOMP._IOwnership _out618;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out619;
            (this).GenExpr(_2287_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out617, out _out618, out _out619);
            _2288_exprGen = _out617;
            _2289___v217 = _out618;
            _2290_recIdents = _out619;
            r = ((_2288_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            RAST._IExpr _out620;
            DCOMP._IOwnership _out621;
            (this).FromOwned(r, expectedOwnership, out _out620, out _out621);
            r = _out620;
            resultingOwnership = _out621;
            readIdents = _2290_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_SeqBoundedPool) {
          DAST._IExpression _2291_of = _source95.dtor_of;
          bool _2292_includeDuplicates = _source95.dtor_includeDuplicates;
          unmatched95 = false;
          {
            RAST._IExpr _2293_exprGen;
            DCOMP._IOwnership _2294___v218;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2295_recIdents;
            RAST._IExpr _out622;
            DCOMP._IOwnership _out623;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out624;
            (this).GenExpr(_2291_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out622, out _out623, out _out624);
            _2293_exprGen = _out622;
            _2294___v218 = _out623;
            _2295_recIdents = _out624;
            r = ((_2293_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            if (!(_2292_includeDuplicates)) {
              r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Itertools"))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("unique"))).Apply1(r);
            }
            RAST._IExpr _out625;
            DCOMP._IOwnership _out626;
            (this).FromOwned(r, expectedOwnership, out _out625, out _out626);
            r = _out625;
            resultingOwnership = _out626;
            readIdents = _2295_recIdents;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapBoundedPool) {
          DAST._IExpression _2296_of = _source95.dtor_of;
          unmatched95 = false;
          {
            RAST._IExpr _2297_exprGen;
            DCOMP._IOwnership _2298___v219;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2299_recIdents;
            RAST._IExpr _out627;
            DCOMP._IOwnership _out628;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out629;
            (this).GenExpr(_2296_of, selfIdent, env, DCOMP.Ownership.create_OwnershipBorrowed(), out _out627, out _out628, out _out629);
            _2297_exprGen = _out627;
            _2298___v219 = _out628;
            _2299_recIdents = _out629;
            r = ((((_2297_exprGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("keys"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements())).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("iter"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
            readIdents = _2299_recIdents;
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
          DAST._IExpression _2300_lo = _source95.dtor_lo;
          DAST._IExpression _2301_hi = _source95.dtor_hi;
          bool _2302_up = _source95.dtor_up;
          unmatched95 = false;
          {
            RAST._IExpr _2303_lo;
            DCOMP._IOwnership _2304___v220;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2305_recIdentsLo;
            RAST._IExpr _out632;
            DCOMP._IOwnership _out633;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out634;
            (this).GenExpr(_2300_lo, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out632, out _out633, out _out634);
            _2303_lo = _out632;
            _2304___v220 = _out633;
            _2305_recIdentsLo = _out634;
            RAST._IExpr _2306_hi;
            DCOMP._IOwnership _2307___v221;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2308_recIdentsHi;
            RAST._IExpr _out635;
            DCOMP._IOwnership _out636;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out637;
            (this).GenExpr(_2301_hi, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out635, out _out636, out _out637);
            _2306_hi = _out635;
            _2307___v221 = _out636;
            _2308_recIdentsHi = _out637;
            if (_2302_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2303_lo, _2306_hi));
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements(_2306_hi, _2303_lo));
            }
            RAST._IExpr _out638;
            DCOMP._IOwnership _out639;
            (this).FromOwned(r, expectedOwnership, out _out638, out _out639);
            r = _out638;
            resultingOwnership = _out639;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2305_recIdentsLo, _2308_recIdentsHi);
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_UnboundedIntRange) {
          DAST._IExpression _2309_start = _source95.dtor_start;
          bool _2310_up = _source95.dtor_up;
          unmatched95 = false;
          {
            RAST._IExpr _2311_start;
            DCOMP._IOwnership _2312___v222;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2313_recIdentStart;
            RAST._IExpr _out640;
            DCOMP._IOwnership _out641;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out642;
            (this).GenExpr(_2309_start, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out640, out _out641, out _out642);
            _2311_start = _out640;
            _2312___v222 = _out641;
            _2313_recIdentStart = _out642;
            if (_2310_up) {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_unbounded"))).Apply1(_2311_start);
            } else {
              r = ((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("integer_range_down_unbounded"))).Apply1(_2311_start);
            }
            RAST._IExpr _out643;
            DCOMP._IOwnership _out644;
            (this).FromOwned(r, expectedOwnership, out _out643, out _out644);
            r = _out643;
            resultingOwnership = _out644;
            readIdents = _2313_recIdentStart;
            return ;
          }
        }
      }
      if (unmatched95) {
        if (_source95.is_MapBuilder) {
          DAST._IType _2314_keyType = _source95.dtor_keyType;
          DAST._IType _2315_valueType = _source95.dtor_valueType;
          unmatched95 = false;
          {
            RAST._IType _2316_kType;
            RAST._IType _out645;
            _out645 = (this).GenType(_2314_keyType, DCOMP.GenTypeContext.@default());
            _2316_kType = _out645;
            RAST._IType _2317_vType;
            RAST._IType _out646;
            _out646 = (this).GenType(_2315_valueType, DCOMP.GenTypeContext.@default());
            _2317_vType = _out646;
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("MapBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2316_kType, _2317_vType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
          DAST._IType _2318_elemType = _source95.dtor_elemType;
          unmatched95 = false;
          {
            RAST._IType _2319_eType;
            RAST._IType _out649;
            _out649 = (this).GenType(_2318_elemType, DCOMP.GenTypeContext.@default());
            _2319_eType = _out649;
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.FromElements();
            r = ((((RAST.__default.dafny__runtime).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("SetBuilder"))).ApplyType(Dafny.Sequence<RAST._IType>.FromElements(_2319_eType))).MSel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("new"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements());
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
        DAST._IType _2320_elemType = _source95.dtor_elemType;
        DAST._IExpression _2321_collection = _source95.dtor_collection;
        bool _2322_is__forall = _source95.dtor_is__forall;
        DAST._IExpression _2323_lambda = _source95.dtor_lambda;
        unmatched95 = false;
        {
          RAST._IType _2324_tpe;
          RAST._IType _out652;
          _out652 = (this).GenType(_2320_elemType, DCOMP.GenTypeContext.@default());
          _2324_tpe = _out652;
          RAST._IExpr _2325_collectionGen;
          DCOMP._IOwnership _2326___v223;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2327_recIdents;
          RAST._IExpr _out653;
          DCOMP._IOwnership _out654;
          Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out655;
          (this).GenExpr(_2321_collection, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out653, out _out654, out _out655);
          _2325_collectionGen = _out653;
          _2326___v223 = _out654;
          _2327_recIdents = _out655;
          Dafny.ISequence<DAST._IAttribute> _2328_extraAttributes;
          _2328_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements();
          if ((((_2321_collection).is_IntRange) || ((_2321_collection).is_UnboundedIntRange)) || ((_2321_collection).is_SeqBoundedPool)) {
            _2328_extraAttributes = Dafny.Sequence<DAST._IAttribute>.FromElements(DCOMP.__default.AttributeOwned);
          }
          if ((_2323_lambda).is_Lambda) {
            Dafny.ISequence<DAST._IFormal> _2329_formals;
            _2329_formals = (_2323_lambda).dtor_params;
            Dafny.ISequence<DAST._IFormal> _2330_newFormals;
            _2330_newFormals = Dafny.Sequence<DAST._IFormal>.FromElements();
            BigInteger _hi49 = new BigInteger((_2329_formals).Count);
            for (BigInteger _2331_i = BigInteger.Zero; _2331_i < _hi49; _2331_i++) {
              var _pat_let_tv141 = _2328_extraAttributes;
              var _pat_let_tv142 = _2329_formals;
              _2330_newFormals = Dafny.Sequence<DAST._IFormal>.Concat(_2330_newFormals, Dafny.Sequence<DAST._IFormal>.FromElements(Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>((_2329_formals).Select(_2331_i), _pat_let38_0 => Dafny.Helpers.Let<DAST._IFormal, DAST._IFormal>(_pat_let38_0, _2332_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(Dafny.Sequence<DAST._IAttribute>.Concat(_pat_let_tv141, ((_pat_let_tv142).Select(_2331_i)).dtor_attributes), _pat_let39_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IAttribute>, DAST._IFormal>(_pat_let39_0, _2333_dt__update_hattributes_h0 => DAST.Formal.create((_2332_dt__update__tmp_h0).dtor_name, (_2332_dt__update__tmp_h0).dtor_typ, _2333_dt__update_hattributes_h0)))))));
            }
            var _pat_let_tv143 = _2330_newFormals;
            DAST._IExpression _2334_newLambda;
            _2334_newLambda = Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_2323_lambda, _pat_let40_0 => Dafny.Helpers.Let<DAST._IExpression, DAST._IExpression>(_pat_let40_0, _2335_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let_tv143, _pat_let41_0 => Dafny.Helpers.Let<Dafny.ISequence<DAST._IFormal>, DAST._IExpression>(_pat_let41_0, _2336_dt__update_hparams_h0 => DAST.Expression.create_Lambda(_2336_dt__update_hparams_h0, (_2335_dt__update__tmp_h1).dtor_retType, (_2335_dt__update__tmp_h1).dtor_body)))));
            RAST._IExpr _2337_lambdaGen;
            DCOMP._IOwnership _2338___v224;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _2339_recLambdaIdents;
            RAST._IExpr _out656;
            DCOMP._IOwnership _out657;
            Dafny.ISet<Dafny.ISequence<Dafny.Rune>> _out658;
            (this).GenExpr(_2334_newLambda, selfIdent, env, DCOMP.Ownership.create_OwnershipOwned(), out _out656, out _out657, out _out658);
            _2337_lambdaGen = _out656;
            _2338___v224 = _out657;
            _2339_recLambdaIdents = _out658;
            Dafny.ISequence<Dafny.Rune> _2340_fn;
            _2340_fn = ((_2322_is__forall) ? (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("all")) : (Dafny.Sequence<Dafny.Rune>.UnicodeFromString("any")));
            r = ((_2325_collectionGen).Sel(_2340_fn)).Apply1(((_2337_lambdaGen).Sel(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("as_ref"))).Apply(Dafny.Sequence<RAST._IExpr>.FromElements()));
            readIdents = Dafny.Set<Dafny.ISequence<Dafny.Rune>>.Union(_2327_recIdents, _2339_recLambdaIdents);
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
      BigInteger _2341_i;
      _2341_i = BigInteger.Zero;
      while ((_2341_i) < (new BigInteger((p).Count))) {
        Dafny.ISequence<Dafny.Rune> _2342_generated = Dafny.Sequence<Dafny.Rune>.Empty;
        RAST._IMod _2343_m;
        RAST._IMod _out661;
        _out661 = (this).GenModule((p).Select(_2341_i), Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.FromElements());
        _2343_m = _out661;
        _2342_generated = (_2343_m)._ToString(Dafny.Sequence<Dafny.Rune>.UnicodeFromString(""));
        if ((_2341_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, _2342_generated);
        _2341_i = (_2341_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<Dafny.Rune> EmitCallToMain(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> fullName)
    {
      Dafny.ISequence<Dafny.Rune> s = Dafny.Sequence<Dafny.Rune>.Empty;
      s = Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\nfn main() {\n");
      BigInteger _2344_i;
      _2344_i = BigInteger.Zero;
      while ((_2344_i) < (new BigInteger((fullName).Count))) {
        if ((_2344_i).Sign == 1) {
          s = Dafny.Sequence<Dafny.Rune>.Concat(s, Dafny.Sequence<Dafny.Rune>.UnicodeFromString("::"));
        }
        s = Dafny.Sequence<Dafny.Rune>.Concat(s, DCOMP.__default.escapeName((fullName).Select(_2344_i)));
        _2344_i = (_2344_i) + (BigInteger.One);
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